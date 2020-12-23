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
% DateTime   : Thu Dec  3 09:53:05 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   44 (  76 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_18,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_22,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,B_24)
      | k4_xboole_0(k1_tarski(A_23),B_24) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_80,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_77])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_80])).

tff(c_85,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_39,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),B_16) = k1_xboole_0
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_39,c_4])).

tff(c_86,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_20,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_20])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_117])).

tff(c_122,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_125,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tarski(A_33),B_34)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_167,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(k1_tarski(A_45),B_46) = k1_xboole_0
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_125,c_4])).

tff(c_123,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_164,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_16])).

tff(c_176,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_164])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  
% 1.91/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.26  %$ r2_hidden > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.91/1.26  
% 1.91/1.26  %Foreground sorts:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Background operators:
% 1.91/1.26  
% 1.91/1.26  
% 1.91/1.26  %Foreground operators:
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.26  
% 1.91/1.27  tff(f_44, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.91/1.27  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.91/1.27  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.91/1.27  tff(c_18, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.27  tff(c_32, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_18])).
% 1.91/1.27  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.27  tff(c_63, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22])).
% 1.91/1.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.27  tff(c_44, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.27  tff(c_77, plain, (![A_23, B_24]: (r2_hidden(A_23, B_24) | k4_xboole_0(k1_tarski(A_23), B_24)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_44])).
% 1.91/1.27  tff(c_80, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_63, c_77])).
% 1.91/1.27  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_80])).
% 1.91/1.27  tff(c_85, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 1.91/1.27  tff(c_39, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.27  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.27  tff(c_43, plain, (![A_15, B_16]: (k4_xboole_0(k1_tarski(A_15), B_16)=k1_xboole_0 | ~r2_hidden(A_15, B_16))), inference(resolution, [status(thm)], [c_39, c_4])).
% 1.91/1.27  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 1.91/1.27  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.27  tff(c_114, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_86, c_20])).
% 1.91/1.27  tff(c_117, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_43, c_114])).
% 1.91/1.27  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_117])).
% 1.91/1.27  tff(c_122, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.27  tff(c_125, plain, (![A_33, B_34]: (r1_tarski(k1_tarski(A_33), B_34) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.27  tff(c_167, plain, (![A_45, B_46]: (k4_xboole_0(k1_tarski(A_45), B_46)=k1_xboole_0 | ~r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_125, c_4])).
% 1.91/1.27  tff(c_123, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.27  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.27  tff(c_164, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_16])).
% 1.91/1.27  tff(c_176, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_164])).
% 1.91/1.27  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_176])).
% 1.91/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.27  
% 1.91/1.27  Inference rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Ref     : 0
% 1.91/1.27  #Sup     : 32
% 1.91/1.27  #Fact    : 0
% 1.91/1.27  #Define  : 0
% 1.91/1.27  #Split   : 2
% 1.91/1.27  #Chain   : 0
% 1.91/1.27  #Close   : 0
% 1.91/1.27  
% 1.91/1.27  Ordering : KBO
% 1.91/1.27  
% 1.91/1.27  Simplification rules
% 1.91/1.27  ----------------------
% 1.91/1.27  #Subsume      : 3
% 1.91/1.27  #Demod        : 4
% 1.91/1.27  #Tautology    : 24
% 1.91/1.27  #SimpNegUnit  : 2
% 1.91/1.27  #BackRed      : 0
% 1.91/1.27  
% 1.91/1.27  #Partial instantiations: 0
% 1.91/1.27  #Strategies tried      : 1
% 1.91/1.27  
% 1.91/1.27  Timing (in seconds)
% 1.91/1.27  ----------------------
% 1.91/1.27  Preprocessing        : 0.30
% 1.91/1.27  Parsing              : 0.16
% 1.91/1.28  CNF conversion       : 0.02
% 1.91/1.28  Main loop            : 0.14
% 1.91/1.28  Inferencing          : 0.06
% 1.91/1.28  Reduction            : 0.04
% 1.91/1.28  Demodulation         : 0.02
% 1.91/1.28  BG Simplification    : 0.01
% 1.91/1.28  Subsumption          : 0.02
% 1.91/1.28  Abstraction          : 0.01
% 1.91/1.28  MUC search           : 0.00
% 1.91/1.28  Cooper               : 0.00
% 1.91/1.28  Total                : 0.47
% 1.91/1.28  Index Insertion      : 0.00
% 1.91/1.28  Index Deletion       : 0.00
% 1.91/1.28  Index Matching       : 0.00
% 1.91/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
