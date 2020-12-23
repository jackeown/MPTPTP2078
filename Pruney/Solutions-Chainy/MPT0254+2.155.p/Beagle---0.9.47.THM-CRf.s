%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:38 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   38 (  94 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 ( 109 expanded)
%              Number of equality atoms :   14 (  68 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_21,plain,(
    ! [A_13,B_14] :
      ( k1_xboole_0 = A_13
      | k2_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_21])).

tff(c_26,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_14])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_26])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | ~ r1_xboole_0(k1_tarski(A_15),B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39,plain,(
    ! [A_15] : ~ r2_hidden(A_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_72,plain,(
    ! [A_15] : ~ r2_hidden(A_15,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_39])).

tff(c_75,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_70,plain,(
    ! [A_5] : k2_xboole_0('#skF_2',A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_55])).

tff(c_73,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_25])).

tff(c_95,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_24),B_25),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [B_25] :
      ( r2_hidden('#skF_1',B_25)
      | ~ r1_tarski(k2_xboole_0('#skF_2',B_25),B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_95])).

tff(c_121,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_1',B_31)
      | ~ r1_tarski(B_31,B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_98])).

tff(c_124,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_121])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.09  
% 1.63/1.09  %Foreground sorts:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Background operators:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Foreground operators:
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.63/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.09  
% 1.63/1.10  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.63/1.10  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.63/1.10  tff(f_50, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.63/1.10  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.63/1.10  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.63/1.10  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.63/1.10  tff(f_41, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 1.63/1.10  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.10  tff(c_51, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.10  tff(c_55, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_51])).
% 1.63/1.10  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.63/1.10  tff(c_21, plain, (![A_13, B_14]: (k1_xboole_0=A_13 | k2_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.10  tff(c_25, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_21])).
% 1.63/1.10  tff(c_26, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25, c_14])).
% 1.63/1.10  tff(c_56, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_26])).
% 1.63/1.10  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.10  tff(c_31, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | ~r1_xboole_0(k1_tarski(A_15), B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.10  tff(c_39, plain, (![A_15]: (~r2_hidden(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.63/1.10  tff(c_72, plain, (![A_15]: (~r2_hidden(A_15, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_39])).
% 1.63/1.10  tff(c_75, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6])).
% 1.63/1.10  tff(c_70, plain, (![A_5]: (k2_xboole_0('#skF_2', A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_55])).
% 1.63/1.10  tff(c_73, plain, (k1_tarski('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_25])).
% 1.63/1.10  tff(c_95, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | ~r1_tarski(k2_xboole_0(k1_tarski(A_24), B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.63/1.10  tff(c_98, plain, (![B_25]: (r2_hidden('#skF_1', B_25) | ~r1_tarski(k2_xboole_0('#skF_2', B_25), B_25))), inference(superposition, [status(thm), theory('equality')], [c_73, c_95])).
% 1.63/1.10  tff(c_121, plain, (![B_31]: (r2_hidden('#skF_1', B_31) | ~r1_tarski(B_31, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_98])).
% 1.63/1.10  tff(c_124, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_75, c_121])).
% 1.63/1.10  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_124])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 26
% 1.63/1.10  #Fact    : 0
% 1.63/1.11  #Define  : 0
% 1.63/1.11  #Split   : 0
% 1.63/1.11  #Chain   : 0
% 1.63/1.11  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 2
% 1.63/1.11  #Demod        : 12
% 1.63/1.11  #Tautology    : 18
% 1.63/1.11  #SimpNegUnit  : 1
% 1.63/1.11  #BackRed      : 9
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.25
% 1.63/1.11  Parsing              : 0.14
% 1.63/1.11  CNF conversion       : 0.01
% 1.63/1.11  Main loop            : 0.11
% 1.63/1.11  Inferencing          : 0.05
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.02
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.38
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
