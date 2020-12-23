%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:29 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  48 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
     => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_91,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(k1_tarski(A_20),B_21) = B_21
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_16])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_22),B_23),B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_121])).

tff(c_137,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_137])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(A_17,B_18)
      | ~ r1_xboole_0(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_82,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_143,plain,(
    ! [A_17] : ~ r2_hidden(A_17,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_82])).

tff(c_141,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  
% 1.87/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.23  
% 1.87/1.24  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.87/1.24  tff(f_50, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.87/1.24  tff(f_29, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.87/1.24  tff(f_37, axiom, (![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 1.87/1.24  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.87/1.24  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.87/1.24  tff(c_91, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)=B_21 | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.24  tff(c_16, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.24  tff(c_103, plain, (k1_xboole_0='#skF_2' | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_16])).
% 1.87/1.24  tff(c_120, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_103])).
% 1.87/1.24  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.24  tff(c_121, plain, (![A_22, B_23]: (r2_hidden(A_22, B_23) | ~r1_tarski(k2_xboole_0(k1_tarski(A_22), B_23), B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.87/1.24  tff(c_135, plain, (r2_hidden('#skF_1', '#skF_2') | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_121])).
% 1.87/1.24  tff(c_137, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_135])).
% 1.87/1.24  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_137])).
% 1.87/1.24  tff(c_140, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_103])).
% 1.87/1.24  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.24  tff(c_77, plain, (![A_17, B_18]: (~r2_hidden(A_17, B_18) | ~r1_xboole_0(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.24  tff(c_82, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_77])).
% 1.87/1.24  tff(c_143, plain, (![A_17]: (~r2_hidden(A_17, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_82])).
% 1.87/1.24  tff(c_141, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_103])).
% 1.87/1.24  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_141])).
% 1.87/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.24  
% 1.87/1.24  Inference rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Ref     : 0
% 1.87/1.24  #Sup     : 33
% 1.87/1.24  #Fact    : 0
% 1.87/1.24  #Define  : 0
% 1.87/1.24  #Split   : 1
% 1.87/1.24  #Chain   : 0
% 1.87/1.24  #Close   : 0
% 1.87/1.24  
% 1.87/1.24  Ordering : KBO
% 1.87/1.24  
% 1.87/1.24  Simplification rules
% 1.87/1.24  ----------------------
% 1.87/1.24  #Subsume      : 1
% 1.87/1.24  #Demod        : 9
% 1.87/1.24  #Tautology    : 22
% 1.87/1.24  #SimpNegUnit  : 2
% 1.87/1.24  #BackRed      : 6
% 1.87/1.24  
% 1.87/1.24  #Partial instantiations: 0
% 1.87/1.24  #Strategies tried      : 1
% 1.87/1.24  
% 1.87/1.24  Timing (in seconds)
% 1.87/1.24  ----------------------
% 1.87/1.24  Preprocessing        : 0.28
% 1.87/1.24  Parsing              : 0.15
% 1.87/1.24  CNF conversion       : 0.02
% 1.87/1.24  Main loop            : 0.18
% 1.87/1.24  Inferencing          : 0.07
% 1.87/1.24  Reduction            : 0.05
% 1.87/1.24  Demodulation         : 0.04
% 1.87/1.24  BG Simplification    : 0.01
% 1.87/1.24  Subsumption          : 0.03
% 1.87/1.24  Abstraction          : 0.01
% 1.87/1.24  MUC search           : 0.00
% 1.87/1.24  Cooper               : 0.00
% 1.87/1.24  Total                : 0.49
% 1.87/1.24  Index Insertion      : 0.00
% 1.87/1.24  Index Deletion       : 0.00
% 1.87/1.24  Index Matching       : 0.00
% 1.87/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
