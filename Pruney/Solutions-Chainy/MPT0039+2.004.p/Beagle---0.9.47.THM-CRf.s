%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:43 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 125 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( r2_xboole_0(A_16,B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_5'(A_18,B_19),B_19)
      | ~ r2_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_234,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,k4_xboole_0(A_63,B_64))
      | r2_hidden(D_62,B_64)
      | ~ r2_hidden(D_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k4_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_110,plain,(
    ! [D_41,B_42,A_43] :
      ( ~ r2_hidden(D_41,B_42)
      | ~ r2_hidden(D_41,k4_xboole_0(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ! [D_41] :
      ( ~ r2_hidden(D_41,'#skF_6')
      | ~ r2_hidden(D_41,k4_xboole_0('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_110])).

tff(c_273,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,'#skF_7')
      | ~ r2_hidden(D_65,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_234,c_117])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden('#skF_5'(A_18,B_19),A_18)
      | ~ r2_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_473,plain,(
    ! [B_73] :
      ( ~ r2_xboole_0('#skF_7',B_73)
      | ~ r2_hidden('#skF_5'('#skF_7',B_73),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_273,c_38])).

tff(c_478,plain,(
    ~ r2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_473])).

tff(c_481,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_478])).

tff(c_484,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_481])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_292,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,k4_xboole_0('#skF_6','#skF_7'))
      | r2_hidden(D_66,'#skF_6')
      | ~ r2_hidden(D_66,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_234])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_326,plain,(
    ! [D_67] :
      ( r2_hidden(D_67,'#skF_6')
      | ~ r2_hidden(D_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_292,c_14])).

tff(c_489,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_2'('#skF_7',B_74),'#skF_6')
      | r1_tarski('#skF_7',B_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_326])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_495,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_489,c_8])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_484,c_484,c_495])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.30  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_5
% 2.10/1.30  
% 2.10/1.30  %Foreground sorts:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Background operators:
% 2.10/1.30  
% 2.10/1.30  
% 2.10/1.30  %Foreground operators:
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.30  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.10/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.30  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.10/1.30  
% 2.10/1.31  tff(f_71, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 2.10/1.31  tff(f_55, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.10/1.31  tff(f_66, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.10/1.31  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.10/1.31  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.10/1.31  tff(c_42, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.31  tff(c_30, plain, (![A_16, B_17]: (r2_xboole_0(A_16, B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.31  tff(c_40, plain, (![A_18, B_19]: (r2_hidden('#skF_5'(A_18, B_19), B_19) | ~r2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.31  tff(c_234, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, k4_xboole_0(A_63, B_64)) | r2_hidden(D_62, B_64) | ~r2_hidden(D_62, A_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.31  tff(c_44, plain, (k4_xboole_0('#skF_7', '#skF_6')=k4_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.31  tff(c_110, plain, (![D_41, B_42, A_43]: (~r2_hidden(D_41, B_42) | ~r2_hidden(D_41, k4_xboole_0(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.31  tff(c_117, plain, (![D_41]: (~r2_hidden(D_41, '#skF_6') | ~r2_hidden(D_41, k4_xboole_0('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_110])).
% 2.10/1.31  tff(c_273, plain, (![D_65]: (r2_hidden(D_65, '#skF_7') | ~r2_hidden(D_65, '#skF_6'))), inference(resolution, [status(thm)], [c_234, c_117])).
% 2.10/1.31  tff(c_38, plain, (![A_18, B_19]: (~r2_hidden('#skF_5'(A_18, B_19), A_18) | ~r2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.31  tff(c_473, plain, (![B_73]: (~r2_xboole_0('#skF_7', B_73) | ~r2_hidden('#skF_5'('#skF_7', B_73), '#skF_6'))), inference(resolution, [status(thm)], [c_273, c_38])).
% 2.10/1.31  tff(c_478, plain, (~r2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_473])).
% 2.10/1.31  tff(c_481, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_30, c_478])).
% 2.10/1.31  tff(c_484, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_42, c_481])).
% 2.10/1.31  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.31  tff(c_292, plain, (![D_66]: (r2_hidden(D_66, k4_xboole_0('#skF_6', '#skF_7')) | r2_hidden(D_66, '#skF_6') | ~r2_hidden(D_66, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_234])).
% 2.10/1.31  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.31  tff(c_326, plain, (![D_67]: (r2_hidden(D_67, '#skF_6') | ~r2_hidden(D_67, '#skF_7'))), inference(resolution, [status(thm)], [c_292, c_14])).
% 2.10/1.31  tff(c_489, plain, (![B_74]: (r2_hidden('#skF_2'('#skF_7', B_74), '#skF_6') | r1_tarski('#skF_7', B_74))), inference(resolution, [status(thm)], [c_10, c_326])).
% 2.10/1.31  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.31  tff(c_495, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_489, c_8])).
% 2.10/1.31  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_484, c_484, c_495])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 96
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 1
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 9
% 2.10/1.31  #Demod        : 2
% 2.10/1.31  #Tautology    : 15
% 2.10/1.31  #SimpNegUnit  : 3
% 2.10/1.31  #BackRed      : 0
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.29
% 2.10/1.31  Parsing              : 0.15
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.25
% 2.10/1.31  Inferencing          : 0.09
% 2.10/1.31  Reduction            : 0.06
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.02
% 2.10/1.31  Subsumption          : 0.06
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.57
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
