%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,k1_tarski(B_12)) = A_11
      | r2_hidden(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(B_39,A_40) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    ! [B_48,B_49] :
      ( k10_relat_1(B_48,B_49) = k1_xboole_0
      | ~ v1_relat_1(B_48)
      | k4_xboole_0(k2_relat_1(B_48),B_49) != k2_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_149,plain,(
    ! [B_50,B_51] :
      ( k10_relat_1(B_50,k1_tarski(B_51)) = k1_xboole_0
      | ~ v1_relat_1(B_50)
      | r2_hidden(B_51,k2_relat_1(B_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_139])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_166,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,k2_relat_1(B_57))
      | k10_relat_1(B_57,k1_tarski('#skF_1'(A_56,k2_relat_1(B_57)))) = k1_xboole_0
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_149,c_4])).

tff(c_26,plain,(
    ! [C_16] :
      ( k10_relat_1('#skF_3',k1_tarski(C_16)) != k1_xboole_0
      | ~ r2_hidden(C_16,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_173,plain,(
    ! [A_56] :
      ( ~ r2_hidden('#skF_1'(A_56,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_56,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_26])).

tff(c_182,plain,(
    ! [A_58] :
      ( ~ r2_hidden('#skF_1'(A_58,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_58,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_173])).

tff(c_190,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.18  
% 1.67/1.18  %Foreground sorts:
% 1.67/1.18  
% 1.67/1.18  
% 1.67/1.18  %Background operators:
% 1.67/1.18  
% 1.67/1.18  
% 1.67/1.18  %Foreground operators:
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.67/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.67/1.18  
% 1.91/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 1.91/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.19  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.91/1.19  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.91/1.19  tff(c_24, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.19  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k1_tarski(B_12))=A_11 | r2_hidden(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.91/1.19  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.19  tff(c_85, plain, (![B_39, A_40]: (k10_relat_1(B_39, A_40)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.19  tff(c_139, plain, (![B_48, B_49]: (k10_relat_1(B_48, B_49)=k1_xboole_0 | ~v1_relat_1(B_48) | k4_xboole_0(k2_relat_1(B_48), B_49)!=k2_relat_1(B_48))), inference(resolution, [status(thm)], [c_10, c_85])).
% 1.91/1.19  tff(c_149, plain, (![B_50, B_51]: (k10_relat_1(B_50, k1_tarski(B_51))=k1_xboole_0 | ~v1_relat_1(B_50) | r2_hidden(B_51, k2_relat_1(B_50)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_139])).
% 1.91/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.19  tff(c_166, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_relat_1(B_57)) | k10_relat_1(B_57, k1_tarski('#skF_1'(A_56, k2_relat_1(B_57))))=k1_xboole_0 | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_149, c_4])).
% 1.91/1.19  tff(c_26, plain, (![C_16]: (k10_relat_1('#skF_3', k1_tarski(C_16))!=k1_xboole_0 | ~r2_hidden(C_16, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.91/1.19  tff(c_173, plain, (![A_56]: (~r2_hidden('#skF_1'(A_56, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_56, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_26])).
% 1.91/1.19  tff(c_182, plain, (![A_58]: (~r2_hidden('#skF_1'(A_58, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_58, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_173])).
% 1.91/1.19  tff(c_190, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_182])).
% 1.91/1.19  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_190])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 33
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 0
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 1
% 1.91/1.19  #Demod        : 1
% 1.91/1.19  #Tautology    : 18
% 1.91/1.19  #SimpNegUnit  : 1
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.28
% 1.91/1.19  Parsing              : 0.15
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.15
% 1.91/1.19  Inferencing          : 0.07
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.02
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.45
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
