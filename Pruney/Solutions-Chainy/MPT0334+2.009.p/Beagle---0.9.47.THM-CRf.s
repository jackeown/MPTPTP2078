%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   43 (  63 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  72 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),B_30) = k1_tarski(A_29)
      | r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1104,plain,(
    ! [C_113,B_114,A_115] :
      ( k4_xboole_0(k2_xboole_0(C_113,B_114),A_115) = k2_xboole_0(k4_xboole_0(C_113,A_115),B_114)
      | ~ r1_xboole_0(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_61,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_1164,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4')))
    | ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_61])).

tff(c_1216,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1164])).

tff(c_1225,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) != k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1216])).

tff(c_1232,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1225])).

tff(c_957,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden(A_105,k4_xboole_0(B_106,k1_tarski(C_107)))
      | C_107 = A_105
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_998,plain,(
    ! [A_105,C_107,B_106] :
      ( ~ r2_hidden(A_105,k1_tarski(C_107))
      | C_107 = A_105
      | ~ r2_hidden(A_105,B_106) ) ),
    inference(resolution,[status(thm)],[c_957,c_6])).

tff(c_1235,plain,(
    ! [B_106] :
      ( '#skF_3' = '#skF_4'
      | ~ r2_hidden('#skF_4',B_106) ) ),
    inference(resolution,[status(thm)],[c_1232,c_998])).

tff(c_1242,plain,(
    ! [B_106] : ~ r2_hidden('#skF_4',B_106) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1235])).

tff(c_1249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1242,c_1232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.54  
% 3.29/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.54  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.29/1.54  
% 3.29/1.54  %Foreground sorts:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Background operators:
% 3.29/1.54  
% 3.29/1.54  
% 3.29/1.54  %Foreground operators:
% 3.29/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.29/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.54  
% 3.29/1.55  tff(f_84, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 3.29/1.55  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 3.29/1.55  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.29/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.29/1.55  tff(f_53, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 3.29/1.55  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.29/1.55  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.55  tff(c_60, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.55  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), B_30)=k1_tarski(A_29) | r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.55  tff(c_32, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.29/1.55  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.55  tff(c_1104, plain, (![C_113, B_114, A_115]: (k4_xboole_0(k2_xboole_0(C_113, B_114), A_115)=k2_xboole_0(k4_xboole_0(C_113, A_115), B_114) | ~r1_xboole_0(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.55  tff(c_58, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.29/1.55  tff(c_61, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 3.29/1.55  tff(c_1164, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4'))) | ~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1104, c_61])).
% 3.29/1.55  tff(c_1216, plain, (~r1_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1164])).
% 3.29/1.55  tff(c_1225, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))!=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1216])).
% 3.29/1.55  tff(c_1232, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1225])).
% 3.29/1.55  tff(c_957, plain, (![A_105, B_106, C_107]: (r2_hidden(A_105, k4_xboole_0(B_106, k1_tarski(C_107))) | C_107=A_105 | ~r2_hidden(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.29/1.55  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.55  tff(c_998, plain, (![A_105, C_107, B_106]: (~r2_hidden(A_105, k1_tarski(C_107)) | C_107=A_105 | ~r2_hidden(A_105, B_106))), inference(resolution, [status(thm)], [c_957, c_6])).
% 3.29/1.55  tff(c_1235, plain, (![B_106]: ('#skF_3'='#skF_4' | ~r2_hidden('#skF_4', B_106))), inference(resolution, [status(thm)], [c_1232, c_998])).
% 3.29/1.55  tff(c_1242, plain, (![B_106]: (~r2_hidden('#skF_4', B_106))), inference(negUnitSimplification, [status(thm)], [c_60, c_1235])).
% 3.29/1.55  tff(c_1249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1242, c_1232])).
% 3.29/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.55  
% 3.29/1.55  Inference rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Ref     : 0
% 3.29/1.55  #Sup     : 291
% 3.29/1.55  #Fact    : 0
% 3.29/1.55  #Define  : 0
% 3.29/1.55  #Split   : 1
% 3.29/1.55  #Chain   : 0
% 3.29/1.55  #Close   : 0
% 3.29/1.55  
% 3.29/1.55  Ordering : KBO
% 3.29/1.55  
% 3.29/1.55  Simplification rules
% 3.29/1.55  ----------------------
% 3.29/1.55  #Subsume      : 45
% 3.29/1.55  #Demod        : 118
% 3.29/1.55  #Tautology    : 109
% 3.29/1.55  #SimpNegUnit  : 6
% 3.29/1.55  #BackRed      : 4
% 3.29/1.55  
% 3.29/1.55  #Partial instantiations: 0
% 3.29/1.55  #Strategies tried      : 1
% 3.29/1.55  
% 3.29/1.55  Timing (in seconds)
% 3.29/1.55  ----------------------
% 3.29/1.55  Preprocessing        : 0.34
% 3.29/1.55  Parsing              : 0.18
% 3.29/1.55  CNF conversion       : 0.02
% 3.29/1.55  Main loop            : 0.39
% 3.29/1.55  Inferencing          : 0.13
% 3.29/1.55  Reduction            : 0.15
% 3.29/1.55  Demodulation         : 0.12
% 3.29/1.55  BG Simplification    : 0.02
% 3.29/1.55  Subsumption          : 0.07
% 3.29/1.55  Abstraction          : 0.02
% 3.29/1.55  MUC search           : 0.00
% 3.29/1.55  Cooper               : 0.00
% 3.29/1.55  Total                : 0.76
% 3.29/1.55  Index Insertion      : 0.00
% 3.29/1.55  Index Deletion       : 0.00
% 3.29/1.55  Index Matching       : 0.00
% 3.29/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
