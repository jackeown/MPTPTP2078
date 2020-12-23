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
% DateTime   : Thu Dec  3 09:48:44 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_40,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_132,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k1_tarski(A_47),k2_tarski(B_48,C_49)) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_144,plain,(
    ! [A_50,A_51] : k2_xboole_0(k1_tarski(A_50),k1_tarski(A_51)) = k1_enumset1(A_50,A_51,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k4_xboole_0(B_43,A_42)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_106])).

tff(c_118,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_115])).

tff(c_153,plain,(
    k1_enumset1('#skF_4','#skF_3','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_118])).

tff(c_10,plain,(
    ! [E_12,A_6,B_7] : r2_hidden(E_12,k1_enumset1(A_6,B_7,E_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_10])).

tff(c_36,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_179,plain,(
    ! [B_18] : k2_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) = k2_tarski(B_18,B_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_144])).

tff(c_246,plain,(
    ! [B_60] : k2_xboole_0(k1_tarski(B_60),k1_tarski(B_60)) = k1_tarski(B_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_179])).

tff(c_141,plain,(
    ! [A_47,A_16] : k2_xboole_0(k1_tarski(A_47),k1_tarski(A_16)) = k1_enumset1(A_47,A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_270,plain,(
    ! [B_61] : k1_enumset1(B_61,B_61,B_61) = k1_tarski(B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_141])).

tff(c_8,plain,(
    ! [E_12,C_8,B_7,A_6] :
      ( E_12 = C_8
      | E_12 = B_7
      | E_12 = A_6
      | ~ r2_hidden(E_12,k1_enumset1(A_6,B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_330,plain,(
    ! [E_63,B_64] :
      ( E_63 = B_64
      | E_63 = B_64
      | E_63 = B_64
      | ~ r2_hidden(E_63,k1_tarski(B_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_8])).

tff(c_333,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_192,c_330])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_40,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.04/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.04/1.23  
% 2.04/1.24  tff(f_59, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.04/1.24  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.24  tff(f_48, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.04/1.24  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.04/1.24  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.04/1.24  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.04/1.24  tff(f_52, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.24  tff(c_40, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.24  tff(c_34, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.24  tff(c_132, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(B_48, C_49))=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.04/1.24  tff(c_144, plain, (![A_50, A_51]: (k2_xboole_0(k1_tarski(A_50), k1_tarski(A_51))=k1_enumset1(A_50, A_51, A_51))), inference(superposition, [status(thm), theory('equality')], [c_34, c_132])).
% 2.04/1.24  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.24  tff(c_42, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.24  tff(c_106, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k4_xboole_0(B_43, A_42))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.24  tff(c_115, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_106])).
% 2.04/1.24  tff(c_118, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_115])).
% 2.04/1.24  tff(c_153, plain, (k1_enumset1('#skF_4', '#skF_3', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_118])).
% 2.04/1.24  tff(c_10, plain, (![E_12, A_6, B_7]: (r2_hidden(E_12, k1_enumset1(A_6, B_7, E_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.24  tff(c_192, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_10])).
% 2.04/1.24  tff(c_36, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.24  tff(c_179, plain, (![B_18]: (k2_xboole_0(k1_tarski(B_18), k1_tarski(B_18))=k2_tarski(B_18, B_18))), inference(superposition, [status(thm), theory('equality')], [c_36, c_144])).
% 2.04/1.24  tff(c_246, plain, (![B_60]: (k2_xboole_0(k1_tarski(B_60), k1_tarski(B_60))=k1_tarski(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_179])).
% 2.04/1.24  tff(c_141, plain, (![A_47, A_16]: (k2_xboole_0(k1_tarski(A_47), k1_tarski(A_16))=k1_enumset1(A_47, A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_34, c_132])).
% 2.04/1.24  tff(c_270, plain, (![B_61]: (k1_enumset1(B_61, B_61, B_61)=k1_tarski(B_61))), inference(superposition, [status(thm), theory('equality')], [c_246, c_141])).
% 2.04/1.24  tff(c_8, plain, (![E_12, C_8, B_7, A_6]: (E_12=C_8 | E_12=B_7 | E_12=A_6 | ~r2_hidden(E_12, k1_enumset1(A_6, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.24  tff(c_330, plain, (![E_63, B_64]: (E_63=B_64 | E_63=B_64 | E_63=B_64 | ~r2_hidden(E_63, k1_tarski(B_64)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_8])).
% 2.04/1.24  tff(c_333, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_192, c_330])).
% 2.04/1.24  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_40, c_333])).
% 2.04/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  Inference rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Ref     : 0
% 2.04/1.24  #Sup     : 71
% 2.04/1.24  #Fact    : 0
% 2.04/1.24  #Define  : 0
% 2.04/1.24  #Split   : 0
% 2.04/1.24  #Chain   : 0
% 2.04/1.24  #Close   : 0
% 2.04/1.24  
% 2.04/1.24  Ordering : KBO
% 2.04/1.24  
% 2.04/1.24  Simplification rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Subsume      : 0
% 2.04/1.24  #Demod        : 24
% 2.04/1.24  #Tautology    : 54
% 2.04/1.24  #SimpNegUnit  : 3
% 2.04/1.24  #BackRed      : 0
% 2.04/1.24  
% 2.04/1.24  #Partial instantiations: 0
% 2.04/1.24  #Strategies tried      : 1
% 2.04/1.24  
% 2.04/1.24  Timing (in seconds)
% 2.04/1.24  ----------------------
% 2.04/1.24  Preprocessing        : 0.30
% 2.04/1.24  Parsing              : 0.15
% 2.04/1.24  CNF conversion       : 0.02
% 2.04/1.24  Main loop            : 0.19
% 2.04/1.24  Inferencing          : 0.07
% 2.04/1.24  Reduction            : 0.06
% 2.04/1.24  Demodulation         : 0.05
% 2.04/1.24  BG Simplification    : 0.01
% 2.04/1.24  Subsumption          : 0.03
% 2.04/1.24  Abstraction          : 0.01
% 2.04/1.24  MUC search           : 0.00
% 2.04/1.24  Cooper               : 0.00
% 2.04/1.24  Total                : 0.51
% 2.04/1.24  Index Insertion      : 0.00
% 2.04/1.24  Index Deletion       : 0.00
% 2.04/1.24  Index Matching       : 0.00
% 2.04/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
