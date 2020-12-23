%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:39 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_22,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_89,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(B_30,k1_tarski(A_31))
      | r2_hidden(A_31,B_30) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [B_38,A_39] :
      ( k4_xboole_0(B_38,k1_tarski(A_39)) = B_38
      | r2_hidden(A_39,B_38) ) ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    k4_xboole_0(k2_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_23,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_136,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_23])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.66/1.12  
% 1.66/1.12  %Foreground sorts:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Background operators:
% 1.66/1.12  
% 1.66/1.12  
% 1.66/1.12  %Foreground operators:
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.66/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.12  
% 1.79/1.13  tff(f_54, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 1.79/1.13  tff(f_46, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.79/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.79/1.13  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.79/1.13  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.79/1.13  tff(c_22, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.13  tff(c_72, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.79/1.13  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.13  tff(c_89, plain, (![B_30, A_31]: (r1_xboole_0(B_30, k1_tarski(A_31)) | r2_hidden(A_31, B_30))), inference(resolution, [status(thm)], [c_72, c_2])).
% 1.79/1.13  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.79/1.13  tff(c_126, plain, (![B_38, A_39]: (k4_xboole_0(B_38, k1_tarski(A_39))=B_38 | r2_hidden(A_39, B_38))), inference(resolution, [status(thm)], [c_89, c_8])).
% 1.79/1.13  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.79/1.13  tff(c_20, plain, (k4_xboole_0(k2_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.13  tff(c_23, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20])).
% 1.79/1.13  tff(c_136, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_126, c_23])).
% 1.79/1.13  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_136])).
% 1.79/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.13  
% 1.79/1.13  Inference rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Ref     : 0
% 1.79/1.13  #Sup     : 29
% 1.79/1.13  #Fact    : 0
% 1.79/1.13  #Define  : 0
% 1.79/1.13  #Split   : 0
% 1.79/1.13  #Chain   : 0
% 1.79/1.13  #Close   : 0
% 1.79/1.13  
% 1.79/1.13  Ordering : KBO
% 1.79/1.13  
% 1.79/1.13  Simplification rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Subsume      : 2
% 1.79/1.13  #Demod        : 1
% 1.79/1.13  #Tautology    : 16
% 1.79/1.13  #SimpNegUnit  : 1
% 1.79/1.13  #BackRed      : 0
% 1.79/1.13  
% 1.79/1.13  #Partial instantiations: 0
% 1.79/1.13  #Strategies tried      : 1
% 1.79/1.13  
% 1.79/1.13  Timing (in seconds)
% 1.79/1.13  ----------------------
% 1.79/1.14  Preprocessing        : 0.27
% 1.79/1.14  Parsing              : 0.14
% 1.79/1.14  CNF conversion       : 0.02
% 1.79/1.14  Main loop            : 0.11
% 1.79/1.14  Inferencing          : 0.05
% 1.79/1.14  Reduction            : 0.03
% 1.79/1.14  Demodulation         : 0.02
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.01
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.41
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
