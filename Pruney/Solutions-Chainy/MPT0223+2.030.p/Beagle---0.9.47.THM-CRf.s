%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:20 EST 2020

% Result     : Theorem 13.53s
% Output     : CNFRefutation 13.53s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  64 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_89,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_70,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_64,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_210,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [E_32,B_27,C_28] : r2_hidden(E_32,k1_enumset1(E_32,B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_228,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_46])).

tff(c_231,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_228])).

tff(c_72,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_277,plain,(
    ! [D_72,B_73,A_74] :
      ( ~ r2_hidden(D_72,B_73)
      | r2_hidden(D_72,k2_xboole_0(A_74,B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_417,plain,(
    ! [D_90,A_91,B_92] :
      ( ~ r2_hidden(D_90,k3_xboole_0(A_91,B_92))
      | r2_hidden(D_90,A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_277])).

tff(c_797,plain,(
    ! [D_122,B_123,A_124] :
      ( ~ r2_hidden(D_122,k3_xboole_0(B_123,A_124))
      | r2_hidden(D_122,A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_417])).

tff(c_979,plain,(
    ! [D_133] :
      ( ~ r2_hidden(D_133,k1_tarski('#skF_7'))
      | r2_hidden(D_133,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_797])).

tff(c_997,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_231,c_979])).

tff(c_66,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1050,plain,(
    ! [E_136,C_137,B_138,A_139] :
      ( E_136 = C_137
      | E_136 = B_138
      | E_136 = A_139
      | ~ r2_hidden(E_136,k1_enumset1(A_139,B_138,C_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7060,plain,(
    ! [E_327,B_328,A_329] :
      ( E_327 = B_328
      | E_327 = A_329
      | E_327 = A_329
      | ~ r2_hidden(E_327,k2_tarski(A_329,B_328)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1050])).

tff(c_32048,plain,(
    ! [E_767,A_768] :
      ( E_767 = A_768
      | E_767 = A_768
      | E_767 = A_768
      | ~ r2_hidden(E_767,k1_tarski(A_768)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_7060])).

tff(c_32359,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_997,c_32048])).

tff(c_32465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_70,c_70,c_32359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.53/6.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/6.20  
% 13.53/6.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/6.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_8 > #skF_5
% 13.53/6.20  
% 13.53/6.20  %Foreground sorts:
% 13.53/6.20  
% 13.53/6.20  
% 13.53/6.20  %Background operators:
% 13.53/6.20  
% 13.53/6.20  
% 13.53/6.20  %Foreground operators:
% 13.53/6.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.53/6.20  tff('#skF_4', type, '#skF_4': $i > $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.53/6.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.53/6.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.53/6.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.53/6.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.53/6.20  tff('#skF_7', type, '#skF_7': $i).
% 13.53/6.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 13.53/6.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.53/6.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.53/6.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.53/6.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.53/6.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.53/6.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 13.53/6.20  tff('#skF_8', type, '#skF_8': $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.53/6.20  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.53/6.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.53/6.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.53/6.20  
% 13.53/6.21  tff(f_96, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 13.53/6.21  tff(f_87, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.53/6.21  tff(f_89, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.53/6.21  tff(f_85, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 13.53/6.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.53/6.21  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 13.53/6.21  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 13.53/6.21  tff(c_70, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.53/6.21  tff(c_64, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.53/6.21  tff(c_210, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.53/6.21  tff(c_46, plain, (![E_32, B_27, C_28]: (r2_hidden(E_32, k1_enumset1(E_32, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.53/6.21  tff(c_228, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_210, c_46])).
% 13.53/6.21  tff(c_231, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_228])).
% 13.53/6.21  tff(c_72, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.53/6.21  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.53/6.21  tff(c_30, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.53/6.21  tff(c_277, plain, (![D_72, B_73, A_74]: (~r2_hidden(D_72, B_73) | r2_hidden(D_72, k2_xboole_0(A_74, B_73)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.53/6.21  tff(c_417, plain, (![D_90, A_91, B_92]: (~r2_hidden(D_90, k3_xboole_0(A_91, B_92)) | r2_hidden(D_90, A_91))), inference(superposition, [status(thm), theory('equality')], [c_30, c_277])).
% 13.53/6.21  tff(c_797, plain, (![D_122, B_123, A_124]: (~r2_hidden(D_122, k3_xboole_0(B_123, A_124)) | r2_hidden(D_122, A_124))), inference(superposition, [status(thm), theory('equality')], [c_2, c_417])).
% 13.53/6.21  tff(c_979, plain, (![D_133]: (~r2_hidden(D_133, k1_tarski('#skF_7')) | r2_hidden(D_133, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_797])).
% 13.53/6.21  tff(c_997, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_231, c_979])).
% 13.53/6.21  tff(c_66, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.53/6.21  tff(c_1050, plain, (![E_136, C_137, B_138, A_139]: (E_136=C_137 | E_136=B_138 | E_136=A_139 | ~r2_hidden(E_136, k1_enumset1(A_139, B_138, C_137)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.53/6.21  tff(c_7060, plain, (![E_327, B_328, A_329]: (E_327=B_328 | E_327=A_329 | E_327=A_329 | ~r2_hidden(E_327, k2_tarski(A_329, B_328)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1050])).
% 13.53/6.21  tff(c_32048, plain, (![E_767, A_768]: (E_767=A_768 | E_767=A_768 | E_767=A_768 | ~r2_hidden(E_767, k1_tarski(A_768)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_7060])).
% 13.53/6.21  tff(c_32359, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_997, c_32048])).
% 13.53/6.21  tff(c_32465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_70, c_70, c_32359])).
% 13.53/6.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.53/6.21  
% 13.53/6.21  Inference rules
% 13.53/6.21  ----------------------
% 13.53/6.21  #Ref     : 8
% 13.53/6.21  #Sup     : 8072
% 13.53/6.21  #Fact    : 48
% 13.53/6.21  #Define  : 0
% 13.53/6.21  #Split   : 8
% 13.53/6.21  #Chain   : 0
% 13.53/6.21  #Close   : 0
% 13.53/6.21  
% 13.53/6.21  Ordering : KBO
% 13.53/6.21  
% 13.53/6.21  Simplification rules
% 13.53/6.21  ----------------------
% 13.53/6.21  #Subsume      : 3479
% 13.53/6.21  #Demod        : 2923
% 13.53/6.21  #Tautology    : 1784
% 13.53/6.21  #SimpNegUnit  : 135
% 13.53/6.21  #BackRed      : 22
% 13.53/6.21  
% 13.53/6.21  #Partial instantiations: 0
% 13.53/6.21  #Strategies tried      : 1
% 13.53/6.21  
% 13.53/6.21  Timing (in seconds)
% 13.53/6.21  ----------------------
% 13.53/6.21  Preprocessing        : 0.33
% 13.53/6.21  Parsing              : 0.16
% 13.53/6.21  CNF conversion       : 0.02
% 13.53/6.21  Main loop            : 5.12
% 13.53/6.21  Inferencing          : 0.96
% 13.53/6.21  Reduction            : 2.07
% 13.53/6.21  Demodulation         : 1.67
% 13.53/6.21  BG Simplification    : 0.11
% 13.53/6.21  Subsumption          : 1.71
% 13.53/6.21  Abstraction          : 0.18
% 13.53/6.21  MUC search           : 0.00
% 13.53/6.21  Cooper               : 0.00
% 13.53/6.21  Total                : 5.47
% 13.53/6.21  Index Insertion      : 0.00
% 13.53/6.21  Index Deletion       : 0.00
% 13.53/6.21  Index Matching       : 0.00
% 13.53/6.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
