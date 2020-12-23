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
% DateTime   : Thu Dec  3 09:53:06 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  64 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(c_10,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_14,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | k4_xboole_0(k1_tarski(A_2),B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_4])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_46])).

tff(c_57,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_56,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(k1_tarski(A_2),B_3) = k1_xboole_0
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_65])).

tff(c_70,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_70])).

tff(c_98,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_113,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(k1_tarski(A_12),B_13) = k1_xboole_0
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_8,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_110,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_8])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_110])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:59:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  
% 1.72/1.19  tff(f_36, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 1.72/1.19  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.72/1.19  tff(c_10, plain, (r2_hidden('#skF_1', '#skF_2') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.72/1.19  tff(c_15, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_10])).
% 1.72/1.19  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2') | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.72/1.19  tff(c_39, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14])).
% 1.72/1.19  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | k4_xboole_0(k1_tarski(A_2), B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.19  tff(c_46, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_39, c_4])).
% 1.72/1.19  tff(c_55, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_46])).
% 1.72/1.19  tff(c_57, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14])).
% 1.72/1.19  tff(c_56, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_14])).
% 1.72/1.19  tff(c_6, plain, (![A_2, B_3]: (k4_xboole_0(k1_tarski(A_2), B_3)=k1_xboole_0 | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.19  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.72/1.19  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 1.72/1.19  tff(c_65, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_58])).
% 1.72/1.19  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_65])).
% 1.72/1.19  tff(c_70, plain, (k4_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.72/1.19  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_70])).
% 1.72/1.19  tff(c_98, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_10])).
% 1.72/1.19  tff(c_113, plain, (![A_12, B_13]: (k4_xboole_0(k1_tarski(A_12), B_13)=k1_xboole_0 | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.19  tff(c_99, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_10])).
% 1.72/1.19  tff(c_8, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0 | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.72/1.19  tff(c_110, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_8])).
% 1.72/1.19  tff(c_122, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_113, c_110])).
% 1.72/1.19  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_122])).
% 1.72/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  Inference rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Ref     : 0
% 1.72/1.19  #Sup     : 24
% 1.72/1.19  #Fact    : 0
% 1.72/1.19  #Define  : 0
% 1.72/1.19  #Split   : 3
% 1.72/1.19  #Chain   : 0
% 1.72/1.19  #Close   : 0
% 1.72/1.19  
% 1.72/1.19  Ordering : KBO
% 1.72/1.19  
% 1.72/1.19  Simplification rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Subsume      : 4
% 1.72/1.19  #Demod        : 7
% 1.72/1.19  #Tautology    : 16
% 1.72/1.19  #SimpNegUnit  : 2
% 1.72/1.19  #BackRed      : 0
% 1.72/1.19  
% 1.72/1.19  #Partial instantiations: 0
% 1.72/1.19  #Strategies tried      : 1
% 1.72/1.19  
% 1.72/1.19  Timing (in seconds)
% 1.72/1.19  ----------------------
% 1.72/1.19  Preprocessing        : 0.25
% 1.72/1.19  Parsing              : 0.13
% 1.72/1.19  CNF conversion       : 0.01
% 1.72/1.19  Main loop            : 0.10
% 1.72/1.19  Inferencing          : 0.04
% 1.72/1.19  Reduction            : 0.03
% 1.72/1.19  Demodulation         : 0.01
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.19  Subsumption          : 0.01
% 1.72/1.19  Abstraction          : 0.01
% 1.72/1.19  MUC search           : 0.00
% 1.72/1.19  Cooper               : 0.00
% 1.72/1.19  Total                : 0.37
% 1.72/1.19  Index Insertion      : 0.00
% 1.72/1.19  Index Deletion       : 0.00
% 1.72/1.19  Index Matching       : 0.00
% 1.72/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
