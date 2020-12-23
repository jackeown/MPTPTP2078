%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | k2_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_51])).

tff(c_88,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden(A_25,B_26)
      | ~ r1_xboole_0(k1_tarski(A_25),B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [B_26] :
      ( ~ r2_hidden('#skF_3',B_26)
      | ~ r1_xboole_0(k1_xboole_0,B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_88])).

tff(c_93,plain,(
    ! [B_26] : ~ r2_hidden('#skF_3',B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_91])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.68/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.68/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.12  
% 1.68/1.13  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.68/1.13  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.68/1.13  tff(f_51, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.68/1.13  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.68/1.13  tff(f_47, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.68/1.13  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.68/1.13  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.13  tff(c_37, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.13  tff(c_40, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 1.68/1.13  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.68/1.13  tff(c_51, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | k2_xboole_0(A_20, B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.13  tff(c_55, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_51])).
% 1.68/1.13  tff(c_88, plain, (![A_25, B_26]: (~r2_hidden(A_25, B_26) | ~r1_xboole_0(k1_tarski(A_25), B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.13  tff(c_91, plain, (![B_26]: (~r2_hidden('#skF_3', B_26) | ~r1_xboole_0(k1_xboole_0, B_26))), inference(superposition, [status(thm), theory('equality')], [c_55, c_88])).
% 1.68/1.13  tff(c_93, plain, (![B_26]: (~r2_hidden('#skF_3', B_26))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_91])).
% 1.68/1.13  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.68/1.13  tff(c_60, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_55, c_10])).
% 1.68/1.13  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_60])).
% 1.68/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  Inference rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Ref     : 0
% 1.68/1.13  #Sup     : 18
% 1.68/1.13  #Fact    : 0
% 1.68/1.13  #Define  : 0
% 1.68/1.13  #Split   : 0
% 1.68/1.13  #Chain   : 0
% 1.68/1.13  #Close   : 0
% 1.68/1.13  
% 1.68/1.13  Ordering : KBO
% 1.68/1.13  
% 1.68/1.13  Simplification rules
% 1.68/1.13  ----------------------
% 1.68/1.13  #Subsume      : 0
% 1.68/1.13  #Demod        : 2
% 1.68/1.13  #Tautology    : 13
% 1.68/1.13  #SimpNegUnit  : 1
% 1.68/1.13  #BackRed      : 2
% 1.68/1.13  
% 1.68/1.13  #Partial instantiations: 0
% 1.68/1.13  #Strategies tried      : 1
% 1.68/1.13  
% 1.68/1.13  Timing (in seconds)
% 1.68/1.13  ----------------------
% 1.68/1.13  Preprocessing        : 0.29
% 1.68/1.13  Parsing              : 0.15
% 1.68/1.13  CNF conversion       : 0.02
% 1.68/1.13  Main loop            : 0.09
% 1.68/1.13  Inferencing          : 0.03
% 1.68/1.13  Reduction            : 0.03
% 1.68/1.13  Demodulation         : 0.02
% 1.68/1.13  BG Simplification    : 0.01
% 1.68/1.13  Subsumption          : 0.01
% 1.68/1.13  Abstraction          : 0.01
% 1.68/1.13  MUC search           : 0.00
% 1.68/1.13  Cooper               : 0.00
% 1.68/1.13  Total                : 0.40
% 1.68/1.13  Index Insertion      : 0.00
% 1.68/1.13  Index Deletion       : 0.00
% 1.68/1.13  Index Matching       : 0.00
% 1.68/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
