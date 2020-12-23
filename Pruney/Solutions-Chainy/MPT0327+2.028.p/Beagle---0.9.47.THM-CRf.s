%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:34 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_12,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_64,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_13])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.05  
% 1.60/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.06  %$ r2_hidden > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.60/1.06  
% 1.60/1.06  %Foreground sorts:
% 1.60/1.06  
% 1.60/1.06  
% 1.60/1.06  %Background operators:
% 1.60/1.06  
% 1.60/1.06  
% 1.60/1.06  %Foreground operators:
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.06  
% 1.60/1.07  tff(f_40, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 1.60/1.07  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.60/1.07  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.60/1.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.60/1.07  tff(c_12, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.07  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.07  tff(c_53, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.07  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.07  tff(c_10, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.07  tff(c_13, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10])).
% 1.60/1.07  tff(c_64, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53, c_13])).
% 1.60/1.07  tff(c_68, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_64])).
% 1.60/1.07  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_68])).
% 1.60/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.07  
% 1.60/1.07  Inference rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Ref     : 0
% 1.60/1.07  #Sup     : 13
% 1.60/1.07  #Fact    : 0
% 1.60/1.07  #Define  : 0
% 1.60/1.07  #Split   : 0
% 1.60/1.07  #Chain   : 0
% 1.60/1.07  #Close   : 0
% 1.60/1.07  
% 1.60/1.07  Ordering : KBO
% 1.60/1.07  
% 1.60/1.07  Simplification rules
% 1.60/1.07  ----------------------
% 1.60/1.07  #Subsume      : 0
% 1.60/1.07  #Demod        : 2
% 1.60/1.07  #Tautology    : 11
% 1.60/1.07  #SimpNegUnit  : 0
% 1.60/1.07  #BackRed      : 0
% 1.60/1.07  
% 1.60/1.07  #Partial instantiations: 0
% 1.60/1.07  #Strategies tried      : 1
% 1.60/1.07  
% 1.60/1.07  Timing (in seconds)
% 1.60/1.07  ----------------------
% 1.60/1.07  Preprocessing        : 0.24
% 1.60/1.07  Parsing              : 0.13
% 1.60/1.07  CNF conversion       : 0.01
% 1.60/1.07  Main loop            : 0.08
% 1.60/1.07  Inferencing          : 0.04
% 1.60/1.07  Reduction            : 0.02
% 1.60/1.07  Demodulation         : 0.02
% 1.60/1.07  BG Simplification    : 0.01
% 1.60/1.07  Subsumption          : 0.01
% 1.60/1.07  Abstraction          : 0.00
% 1.60/1.07  MUC search           : 0.00
% 1.60/1.07  Cooper               : 0.00
% 1.60/1.07  Total                : 0.35
% 1.60/1.07  Index Insertion      : 0.00
% 1.60/1.07  Index Deletion       : 0.00
% 1.60/1.07  Index Matching       : 0.00
% 1.60/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
