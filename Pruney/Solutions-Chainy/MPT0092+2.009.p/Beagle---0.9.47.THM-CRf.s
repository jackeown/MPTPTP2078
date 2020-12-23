%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,(
    ! [D_46,B_47,A_48] :
      ( ~ r2_hidden(D_46,B_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_48,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2072,plain,(
    ! [A_229,B_230,B_231] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_229,B_230),B_231),B_230)
      | r1_xboole_0(k4_xboole_0(A_229,B_230),B_231) ) ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_2100,plain,(
    ! [A_232,B_233] : r1_xboole_0(k4_xboole_0(A_232,B_233),B_233) ),
    inference(resolution,[status(thm)],[c_24,c_2072])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_123,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_xboole_0(A_43,B_44)
      | ~ r1_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_132,plain,(
    ! [A_43] :
      ( r1_xboole_0(A_43,'#skF_4')
      | ~ r1_xboole_0(A_43,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_123])).

tff(c_2146,plain,(
    ! [A_234] : r1_xboole_0(k4_xboole_0(A_234,'#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2100,c_132])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2158,plain,(
    ! [A_234] : r1_xboole_0('#skF_4',k4_xboole_0(A_234,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_2146,c_20])).

tff(c_40,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:18:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.75/1.65  
% 3.75/1.65  %Foreground sorts:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Background operators:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Foreground operators:
% 3.75/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.75/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.75/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.65  
% 3.75/1.66  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.75/1.66  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.75/1.66  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.75/1.66  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.75/1.66  tff(f_81, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.75/1.66  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.75/1.66  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.66  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.75/1.66  tff(c_133, plain, (![D_46, B_47, A_48]: (~r2_hidden(D_46, B_47) | ~r2_hidden(D_46, k4_xboole_0(A_48, B_47)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.66  tff(c_2072, plain, (![A_229, B_230, B_231]: (~r2_hidden('#skF_3'(k4_xboole_0(A_229, B_230), B_231), B_230) | r1_xboole_0(k4_xboole_0(A_229, B_230), B_231))), inference(resolution, [status(thm)], [c_26, c_133])).
% 3.75/1.66  tff(c_2100, plain, (![A_232, B_233]: (r1_xboole_0(k4_xboole_0(A_232, B_233), B_233))), inference(resolution, [status(thm)], [c_24, c_2072])).
% 3.75/1.66  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.75/1.66  tff(c_58, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.75/1.66  tff(c_70, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_58])).
% 3.75/1.66  tff(c_123, plain, (![A_43, B_44, C_45]: (r1_xboole_0(A_43, B_44) | ~r1_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.75/1.66  tff(c_132, plain, (![A_43]: (r1_xboole_0(A_43, '#skF_4') | ~r1_xboole_0(A_43, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_123])).
% 3.75/1.66  tff(c_2146, plain, (![A_234]: (r1_xboole_0(k4_xboole_0(A_234, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_2100, c_132])).
% 3.75/1.66  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.75/1.66  tff(c_2158, plain, (![A_234]: (r1_xboole_0('#skF_4', k4_xboole_0(A_234, '#skF_5')))), inference(resolution, [status(thm)], [c_2146, c_20])).
% 3.75/1.66  tff(c_40, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.75/1.66  tff(c_2201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2158, c_40])).
% 3.75/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.66  
% 3.75/1.66  Inference rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Ref     : 0
% 3.75/1.66  #Sup     : 500
% 3.75/1.66  #Fact    : 0
% 3.75/1.66  #Define  : 0
% 3.75/1.66  #Split   : 4
% 3.75/1.66  #Chain   : 0
% 3.75/1.66  #Close   : 0
% 3.75/1.66  
% 3.75/1.66  Ordering : KBO
% 3.75/1.66  
% 3.75/1.66  Simplification rules
% 3.75/1.66  ----------------------
% 3.75/1.66  #Subsume      : 140
% 3.75/1.66  #Demod        : 207
% 3.75/1.66  #Tautology    : 188
% 3.75/1.66  #SimpNegUnit  : 0
% 3.75/1.66  #BackRed      : 10
% 3.75/1.66  
% 3.75/1.66  #Partial instantiations: 0
% 3.75/1.66  #Strategies tried      : 1
% 3.75/1.66  
% 3.75/1.66  Timing (in seconds)
% 3.75/1.66  ----------------------
% 3.75/1.67  Preprocessing        : 0.30
% 3.75/1.67  Parsing              : 0.17
% 3.75/1.67  CNF conversion       : 0.02
% 3.75/1.67  Main loop            : 0.59
% 3.75/1.67  Inferencing          : 0.22
% 3.75/1.67  Reduction            : 0.16
% 3.75/1.67  Demodulation         : 0.11
% 3.75/1.67  BG Simplification    : 0.02
% 3.75/1.67  Subsumption          : 0.15
% 3.75/1.67  Abstraction          : 0.03
% 3.75/1.67  MUC search           : 0.00
% 3.75/1.67  Cooper               : 0.00
% 3.75/1.67  Total                : 0.92
% 3.75/1.67  Index Insertion      : 0.00
% 3.75/1.67  Index Deletion       : 0.00
% 3.75/1.67  Index Matching       : 0.00
% 3.75/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
