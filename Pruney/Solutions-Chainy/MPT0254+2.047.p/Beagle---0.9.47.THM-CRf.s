%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:25 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   36 (  57 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  54 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    ! [A_21,B_22] :
      ( k1_xboole_0 = A_21
      | k2_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_57])).

tff(c_65,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_106,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_65])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_28] : r1_xboole_0(A_28,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_8])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,B_14)
      | ~ r1_xboole_0(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_180,plain,(
    ! [A_13] : ~ r2_hidden(A_13,'#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_24])).

tff(c_12,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_162,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.02/1.29  
% 2.02/1.29  %Foreground sorts:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Background operators:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Foreground operators:
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.29  
% 2.02/1.30  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.02/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.02/1.30  tff(f_53, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.02/1.30  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.02/1.30  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.30  tff(f_49, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.02/1.30  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.02/1.30  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.30  tff(c_91, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.30  tff(c_26, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.30  tff(c_57, plain, (![A_21, B_22]: (k1_xboole_0=A_21 | k2_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.30  tff(c_64, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_57])).
% 2.02/1.30  tff(c_65, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 2.02/1.30  tff(c_106, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91, c_65])).
% 2.02/1.30  tff(c_152, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_106])).
% 2.02/1.30  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.30  tff(c_175, plain, (![A_28]: (r1_xboole_0(A_28, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_8])).
% 2.02/1.30  tff(c_24, plain, (![A_13, B_14]: (~r2_hidden(A_13, B_14) | ~r1_xboole_0(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.30  tff(c_180, plain, (![A_13]: (~r2_hidden(A_13, '#skF_4'))), inference(resolution, [status(thm)], [c_175, c_24])).
% 2.02/1.30  tff(c_12, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.30  tff(c_72, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_12])).
% 2.02/1.30  tff(c_162, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72])).
% 2.02/1.30  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_162])).
% 2.02/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  Inference rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Ref     : 0
% 2.02/1.30  #Sup     : 45
% 2.02/1.30  #Fact    : 0
% 2.02/1.30  #Define  : 0
% 2.02/1.30  #Split   : 0
% 2.02/1.30  #Chain   : 0
% 2.02/1.30  #Close   : 0
% 2.02/1.30  
% 2.02/1.30  Ordering : KBO
% 2.02/1.30  
% 2.02/1.30  Simplification rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Subsume      : 0
% 2.02/1.30  #Demod        : 18
% 2.02/1.30  #Tautology    : 32
% 2.02/1.30  #SimpNegUnit  : 1
% 2.02/1.30  #BackRed      : 9
% 2.02/1.30  
% 2.02/1.30  #Partial instantiations: 0
% 2.02/1.30  #Strategies tried      : 1
% 2.02/1.30  
% 2.02/1.30  Timing (in seconds)
% 2.02/1.30  ----------------------
% 2.02/1.30  Preprocessing        : 0.32
% 2.02/1.30  Parsing              : 0.16
% 2.02/1.30  CNF conversion       : 0.02
% 2.02/1.30  Main loop            : 0.13
% 2.02/1.30  Inferencing          : 0.04
% 2.02/1.30  Reduction            : 0.05
% 2.02/1.30  Demodulation         : 0.04
% 2.02/1.30  BG Simplification    : 0.01
% 2.02/1.30  Subsumption          : 0.02
% 2.02/1.30  Abstraction          : 0.01
% 2.02/1.30  MUC search           : 0.00
% 2.02/1.30  Cooper               : 0.00
% 2.02/1.30  Total                : 0.48
% 2.02/1.30  Index Insertion      : 0.00
% 2.02/1.30  Index Deletion       : 0.00
% 2.02/1.30  Index Matching       : 0.00
% 2.02/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
