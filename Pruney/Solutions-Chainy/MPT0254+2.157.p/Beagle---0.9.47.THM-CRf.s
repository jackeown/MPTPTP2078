%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:39 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   25 (  37 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  39 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( k1_xboole_0 = A_9
      | k2_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | k4_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_1',B_14)
      | k4_xboole_0(k1_xboole_0,B_14) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_58])).

tff(c_67,plain,(
    ! [B_14] : r2_hidden('#skF_1',B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_69,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden(A_16,B_17)
      | k4_xboole_0(k1_tarski(A_16),B_17) != k1_tarski(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [B_17] :
      ( ~ r2_hidden('#skF_1',B_17)
      | k4_xboole_0(k1_xboole_0,B_17) != k1_tarski('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_69])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4,c_67,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:36:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.21  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.21  
% 1.79/1.21  %Foreground sorts:
% 1.79/1.21  
% 1.79/1.21  
% 1.79/1.21  %Background operators:
% 1.79/1.21  
% 1.79/1.21  
% 1.79/1.21  %Foreground operators:
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.21  
% 1.79/1.22  tff(f_44, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.79/1.22  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.79/1.22  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.79/1.22  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.79/1.22  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.79/1.22  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.79/1.22  tff(c_26, plain, (![A_9, B_10]: (k1_xboole_0=A_9 | k2_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.22  tff(c_30, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_26])).
% 1.79/1.22  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.22  tff(c_58, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | k4_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.22  tff(c_64, plain, (![B_14]: (r2_hidden('#skF_1', B_14) | k4_xboole_0(k1_xboole_0, B_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_58])).
% 1.79/1.22  tff(c_67, plain, (![B_14]: (r2_hidden('#skF_1', B_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 1.79/1.22  tff(c_69, plain, (![A_16, B_17]: (~r2_hidden(A_16, B_17) | k4_xboole_0(k1_tarski(A_16), B_17)!=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.22  tff(c_75, plain, (![B_17]: (~r2_hidden('#skF_1', B_17) | k4_xboole_0(k1_xboole_0, B_17)!=k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_69])).
% 1.79/1.22  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4, c_67, c_75])).
% 1.79/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.22  
% 1.79/1.22  Inference rules
% 1.79/1.22  ----------------------
% 1.79/1.22  #Ref     : 0
% 1.79/1.22  #Sup     : 17
% 1.79/1.22  #Fact    : 0
% 1.79/1.22  #Define  : 0
% 1.79/1.22  #Split   : 0
% 1.79/1.22  #Chain   : 0
% 1.79/1.22  #Close   : 0
% 1.79/1.22  
% 1.79/1.22  Ordering : KBO
% 1.79/1.22  
% 1.79/1.22  Simplification rules
% 1.79/1.22  ----------------------
% 1.79/1.22  #Subsume      : 0
% 1.79/1.22  #Demod        : 6
% 1.79/1.22  #Tautology    : 13
% 1.79/1.22  #SimpNegUnit  : 0
% 1.79/1.22  #BackRed      : 1
% 1.79/1.22  
% 1.79/1.22  #Partial instantiations: 0
% 1.79/1.22  #Strategies tried      : 1
% 1.79/1.22  
% 1.79/1.22  Timing (in seconds)
% 1.79/1.22  ----------------------
% 1.79/1.22  Preprocessing        : 0.30
% 1.79/1.22  Parsing              : 0.15
% 1.79/1.22  CNF conversion       : 0.02
% 1.79/1.22  Main loop            : 0.12
% 1.79/1.22  Inferencing          : 0.05
% 1.79/1.22  Reduction            : 0.03
% 1.79/1.22  Demodulation         : 0.02
% 1.79/1.22  BG Simplification    : 0.01
% 1.79/1.22  Subsumption          : 0.02
% 1.79/1.22  Abstraction          : 0.01
% 1.79/1.22  MUC search           : 0.00
% 1.79/1.22  Cooper               : 0.00
% 1.79/1.22  Total                : 0.45
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
