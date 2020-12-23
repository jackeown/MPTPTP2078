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
% DateTime   : Thu Dec  3 09:54:51 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  39 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_34,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(k2_xboole_0(B_21,k1_tarski(A_20)),k1_tarski(A_20)) = B_21
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_35,plain,(
    ! [B_21,A_20] :
      ( k4_xboole_0(B_21,k1_tarski(A_20)) = B_21
      | r2_hidden(A_20,B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [C_52,B_53,A_54] :
      ( k4_xboole_0(k2_xboole_0(C_52,B_53),A_54) = k2_xboole_0(k4_xboole_0(C_52,A_54),B_53)
      | ~ r1_xboole_0(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_265,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_36])).

tff(c_291,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_298,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) != k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_291])).

tff(c_302,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_298])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_305,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_302,c_14])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.22  %$ r2_hidden > r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.95/1.22  
% 1.95/1.22  %Foreground sorts:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Background operators:
% 1.95/1.22  
% 1.95/1.22  
% 1.95/1.22  %Foreground operators:
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.95/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.95/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.95/1.22  
% 2.10/1.23  tff(f_61, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 2.10/1.23  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.10/1.23  tff(f_55, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 2.10/1.23  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.10/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.10/1.23  tff(f_39, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.10/1.23  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.10/1.23  tff(c_34, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.23  tff(c_30, plain, (![B_21, A_20]: (k4_xboole_0(k2_xboole_0(B_21, k1_tarski(A_20)), k1_tarski(A_20))=B_21 | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.23  tff(c_35, plain, (![B_21, A_20]: (k4_xboole_0(B_21, k1_tarski(A_20))=B_21 | r2_hidden(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_30])).
% 2.10/1.23  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.23  tff(c_247, plain, (![C_52, B_53, A_54]: (k4_xboole_0(k2_xboole_0(C_52, B_53), A_54)=k2_xboole_0(k4_xboole_0(C_52, A_54), B_53) | ~r1_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.23  tff(c_32, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_36, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 2.10/1.23  tff(c_265, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4'))) | ~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_36])).
% 2.10/1.23  tff(c_291, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_265])).
% 2.10/1.23  tff(c_298, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))!=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_10, c_291])).
% 2.10/1.23  tff(c_302, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_298])).
% 2.10/1.23  tff(c_14, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.23  tff(c_305, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_302, c_14])).
% 2.10/1.23  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_305])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 63
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 1
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 2
% 2.10/1.23  #Demod        : 12
% 2.10/1.23  #Tautology    : 35
% 2.10/1.23  #SimpNegUnit  : 1
% 2.10/1.23  #BackRed      : 0
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.15
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.19
% 2.10/1.24  Inferencing          : 0.07
% 2.10/1.24  Reduction            : 0.07
% 2.10/1.24  Demodulation         : 0.05
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.04
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.50
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
