%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 5.38s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  95 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),B_17)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_4'(A_16,B_17),A_16)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_75,plain,(
    ! [D_35,B_36,A_37] :
      ( ~ r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k4_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_231,plain,(
    ! [A_65,B_66,B_67] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_65,B_66),B_67),B_66)
      | r1_xboole_0(k4_xboole_0(A_65,B_66),B_67) ) ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_252,plain,(
    ! [A_68,B_69] : r1_xboole_0(k4_xboole_0(A_68,B_69),B_69) ),
    inference(resolution,[status(thm)],[c_34,c_231])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_259,plain,(
    ! [A_68,B_69] : k3_xboole_0(k4_xboole_0(A_68,B_69),B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_252,c_26])).

tff(c_40,plain,(
    r1_tarski('#skF_5',k4_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,(
    ! [A_16,B_17,B_42] :
      ( r2_hidden('#skF_4'(A_16,B_17),B_42)
      | ~ r1_tarski(B_17,B_42)
      | r1_xboole_0(A_16,B_17) ) ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k3_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_4553,plain,(
    ! [A_334,B_335,A_336] :
      ( ~ r2_hidden('#skF_4'(A_334,B_335),A_336)
      | k3_xboole_0(A_336,B_335) != k1_xboole_0
      | r1_xboole_0(A_334,B_335) ) ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_4853,plain,(
    ! [B_351,B_352,A_353] :
      ( k3_xboole_0(B_351,B_352) != k1_xboole_0
      | ~ r1_tarski(B_352,B_351)
      | r1_xboole_0(A_353,B_352) ) ),
    inference(resolution,[status(thm)],[c_105,c_4553])).

tff(c_4865,plain,(
    ! [A_353] :
      ( k3_xboole_0(k4_xboole_0('#skF_6','#skF_5'),'#skF_5') != k1_xboole_0
      | r1_xboole_0(A_353,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_4853])).

tff(c_4877,plain,(
    ! [A_354] : r1_xboole_0(A_354,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_4865])).

tff(c_4885,plain,(
    ! [A_355] : k3_xboole_0(A_355,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4877,c_26])).

tff(c_30,plain,(
    ! [A_14] : k3_xboole_0(A_14,A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4910,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4885,c_30])).

tff(c_4944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.38/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.06  
% 5.38/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.38/2.06  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.38/2.06  
% 5.38/2.06  %Foreground sorts:
% 5.38/2.06  
% 5.38/2.06  
% 5.38/2.06  %Background operators:
% 5.38/2.06  
% 5.38/2.06  
% 5.38/2.06  %Foreground operators:
% 5.38/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.38/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.38/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.38/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.38/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.38/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.38/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.38/2.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.38/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.38/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.38/2.06  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.38/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.38/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.38/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.38/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.38/2.06  
% 5.70/2.07  tff(f_71, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 5.70/2.07  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.70/2.07  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.70/2.07  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.70/2.07  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.70/2.07  tff(f_48, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.70/2.07  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.70/2.07  tff(c_34, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), B_17) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.70/2.07  tff(c_36, plain, (![A_16, B_17]: (r2_hidden('#skF_4'(A_16, B_17), A_16) | r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.70/2.07  tff(c_75, plain, (![D_35, B_36, A_37]: (~r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k4_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.70/2.07  tff(c_231, plain, (![A_65, B_66, B_67]: (~r2_hidden('#skF_4'(k4_xboole_0(A_65, B_66), B_67), B_66) | r1_xboole_0(k4_xboole_0(A_65, B_66), B_67))), inference(resolution, [status(thm)], [c_36, c_75])).
% 5.70/2.07  tff(c_252, plain, (![A_68, B_69]: (r1_xboole_0(k4_xboole_0(A_68, B_69), B_69))), inference(resolution, [status(thm)], [c_34, c_231])).
% 5.70/2.07  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.70/2.07  tff(c_259, plain, (![A_68, B_69]: (k3_xboole_0(k4_xboole_0(A_68, B_69), B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_252, c_26])).
% 5.70/2.07  tff(c_40, plain, (r1_tarski('#skF_5', k4_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.70/2.07  tff(c_98, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.70/2.07  tff(c_105, plain, (![A_16, B_17, B_42]: (r2_hidden('#skF_4'(A_16, B_17), B_42) | ~r1_tarski(B_17, B_42) | r1_xboole_0(A_16, B_17))), inference(resolution, [status(thm)], [c_34, c_98])).
% 5.70/2.07  tff(c_28, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k3_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.70/2.07  tff(c_108, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.70/2.07  tff(c_112, plain, (![C_47, B_48, A_49]: (~r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_108])).
% 5.70/2.07  tff(c_4553, plain, (![A_334, B_335, A_336]: (~r2_hidden('#skF_4'(A_334, B_335), A_336) | k3_xboole_0(A_336, B_335)!=k1_xboole_0 | r1_xboole_0(A_334, B_335))), inference(resolution, [status(thm)], [c_34, c_112])).
% 5.70/2.07  tff(c_4853, plain, (![B_351, B_352, A_353]: (k3_xboole_0(B_351, B_352)!=k1_xboole_0 | ~r1_tarski(B_352, B_351) | r1_xboole_0(A_353, B_352))), inference(resolution, [status(thm)], [c_105, c_4553])).
% 5.70/2.07  tff(c_4865, plain, (![A_353]: (k3_xboole_0(k4_xboole_0('#skF_6', '#skF_5'), '#skF_5')!=k1_xboole_0 | r1_xboole_0(A_353, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_4853])).
% 5.70/2.07  tff(c_4877, plain, (![A_354]: (r1_xboole_0(A_354, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_4865])).
% 5.70/2.07  tff(c_4885, plain, (![A_355]: (k3_xboole_0(A_355, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_4877, c_26])).
% 5.70/2.07  tff(c_30, plain, (![A_14]: (k3_xboole_0(A_14, A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.70/2.07  tff(c_4910, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_4885, c_30])).
% 5.70/2.07  tff(c_4944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4910])).
% 5.70/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.07  
% 5.70/2.07  Inference rules
% 5.70/2.07  ----------------------
% 5.70/2.07  #Ref     : 0
% 5.70/2.07  #Sup     : 1202
% 5.70/2.07  #Fact    : 0
% 5.70/2.07  #Define  : 0
% 5.70/2.07  #Split   : 0
% 5.70/2.07  #Chain   : 0
% 5.70/2.07  #Close   : 0
% 5.70/2.07  
% 5.70/2.07  Ordering : KBO
% 5.70/2.07  
% 5.70/2.07  Simplification rules
% 5.70/2.07  ----------------------
% 5.70/2.07  #Subsume      : 236
% 5.70/2.07  #Demod        : 434
% 5.70/2.07  #Tautology    : 457
% 5.71/2.07  #SimpNegUnit  : 2
% 5.71/2.07  #BackRed      : 3
% 5.71/2.07  
% 5.71/2.07  #Partial instantiations: 0
% 5.71/2.07  #Strategies tried      : 1
% 5.71/2.07  
% 5.71/2.07  Timing (in seconds)
% 5.71/2.07  ----------------------
% 5.71/2.08  Preprocessing        : 0.30
% 5.71/2.08  Parsing              : 0.15
% 5.71/2.08  CNF conversion       : 0.02
% 5.71/2.08  Main loop            : 1.03
% 5.71/2.08  Inferencing          : 0.32
% 5.71/2.08  Reduction            : 0.28
% 5.71/2.08  Demodulation         : 0.20
% 5.71/2.08  BG Simplification    : 0.04
% 5.71/2.08  Subsumption          : 0.31
% 5.71/2.08  Abstraction          : 0.05
% 5.71/2.08  MUC search           : 0.00
% 5.71/2.08  Cooper               : 0.00
% 5.71/2.08  Total                : 1.35
% 5.71/2.08  Index Insertion      : 0.00
% 5.71/2.08  Index Deletion       : 0.00
% 5.71/2.08  Index Matching       : 0.00
% 5.71/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
