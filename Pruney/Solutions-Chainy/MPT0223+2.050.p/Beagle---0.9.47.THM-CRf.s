%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:23 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  44 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(k1_tarski(A_24),B_25)
      | r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_106,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7'))
      | ~ r2_hidden(C_49,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_106])).

tff(c_127,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_131,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_48,c_127])).

tff(c_30,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_131,c_30])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_134])).

tff(c_142,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_147,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_32,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.17  tff('#skF_7', type, '#skF_7': $i).
% 1.86/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.86/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.17  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.86/1.17  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.86/1.17  
% 1.86/1.17  tff(f_61, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.86/1.17  tff(f_77, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.86/1.17  tff(f_72, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.86/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.17  tff(c_32, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.17  tff(c_50, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.86/1.17  tff(c_48, plain, (![A_24, B_25]: (r1_xboole_0(k1_tarski(A_24), B_25) | r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.17  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.86/1.17  tff(c_106, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.17  tff(c_109, plain, (![C_49]: (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7')) | ~r2_hidden(C_49, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_106])).
% 1.86/1.17  tff(c_127, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_109])).
% 1.86/1.17  tff(c_131, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_48, c_127])).
% 1.86/1.17  tff(c_30, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.17  tff(c_134, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_131, c_30])).
% 1.86/1.17  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_134])).
% 1.86/1.17  tff(c_142, plain, (![C_55]: (~r2_hidden(C_55, k1_tarski('#skF_6')))), inference(splitRight, [status(thm)], [c_109])).
% 1.86/1.17  tff(c_147, plain, $false, inference(resolution, [status(thm)], [c_32, c_142])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 20
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 2
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 0
% 1.86/1.17  #Demod        : 3
% 1.86/1.17  #Tautology    : 13
% 1.86/1.17  #SimpNegUnit  : 1
% 1.86/1.17  #BackRed      : 0
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.96/1.18  Preprocessing        : 0.30
% 1.96/1.18  Parsing              : 0.15
% 1.96/1.18  CNF conversion       : 0.02
% 1.96/1.18  Main loop            : 0.13
% 1.96/1.18  Inferencing          : 0.04
% 1.96/1.18  Reduction            : 0.04
% 1.96/1.18  Demodulation         : 0.03
% 1.96/1.18  BG Simplification    : 0.01
% 1.96/1.18  Subsumption          : 0.03
% 1.96/1.18  Abstraction          : 0.01
% 1.96/1.18  MUC search           : 0.00
% 1.96/1.18  Cooper               : 0.00
% 1.96/1.18  Total                : 0.45
% 1.96/1.18  Index Insertion      : 0.00
% 1.96/1.18  Index Deletion       : 0.00
% 1.96/1.18  Index Matching       : 0.00
% 1.96/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
