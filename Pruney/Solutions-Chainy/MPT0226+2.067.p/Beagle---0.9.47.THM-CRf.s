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
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_20,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_43,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | k4_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47,c_2])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  
% 1.61/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.08  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.61/1.08  
% 1.61/1.08  %Foreground sorts:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Background operators:
% 1.61/1.08  
% 1.61/1.08  
% 1.61/1.08  %Foreground operators:
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.61/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.08  
% 1.61/1.09  tff(f_43, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.61/1.09  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.61/1.09  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.61/1.09  tff(c_20, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.09  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.09  tff(c_43, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | k4_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.09  tff(c_47, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_43])).
% 1.61/1.09  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.09  tff(c_50, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_47, c_2])).
% 1.61/1.09  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_50])).
% 1.61/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  Inference rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Ref     : 0
% 1.61/1.09  #Sup     : 7
% 1.61/1.09  #Fact    : 0
% 1.61/1.09  #Define  : 0
% 1.61/1.09  #Split   : 0
% 1.61/1.09  #Chain   : 0
% 1.61/1.09  #Close   : 0
% 1.61/1.09  
% 1.61/1.09  Ordering : KBO
% 1.61/1.09  
% 1.61/1.09  Simplification rules
% 1.61/1.09  ----------------------
% 1.61/1.09  #Subsume      : 0
% 1.61/1.09  #Demod        : 0
% 1.61/1.09  #Tautology    : 5
% 1.61/1.09  #SimpNegUnit  : 1
% 1.61/1.09  #BackRed      : 0
% 1.61/1.09  
% 1.61/1.09  #Partial instantiations: 0
% 1.61/1.09  #Strategies tried      : 1
% 1.61/1.09  
% 1.61/1.09  Timing (in seconds)
% 1.61/1.09  ----------------------
% 1.61/1.09  Preprocessing        : 0.28
% 1.61/1.09  Parsing              : 0.14
% 1.61/1.09  CNF conversion       : 0.02
% 1.61/1.09  Main loop            : 0.07
% 1.61/1.09  Inferencing          : 0.02
% 1.61/1.09  Reduction            : 0.02
% 1.61/1.10  Demodulation         : 0.01
% 1.61/1.10  BG Simplification    : 0.01
% 1.61/1.10  Subsumption          : 0.01
% 1.61/1.10  Abstraction          : 0.00
% 1.61/1.10  MUC search           : 0.00
% 1.61/1.10  Cooper               : 0.00
% 1.61/1.10  Total                : 0.37
% 1.61/1.10  Index Insertion      : 0.00
% 1.61/1.10  Index Deletion       : 0.00
% 1.61/1.10  Index Matching       : 0.00
% 1.61/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
