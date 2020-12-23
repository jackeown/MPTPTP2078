%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  65 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    ! [C_22,B_23,A_24] :
      ( r2_hidden(C_22,B_23)
      | ~ r2_hidden(C_22,A_24)
      | ~ r1_tarski(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_36,B_37,B_38] :
      ( r2_hidden('#skF_2'(A_36,B_37),B_38)
      | ~ r1_tarski(A_36,B_38)
      | r1_xboole_0(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_51,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,B_26)
      | ~ r2_hidden(C_27,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [C_27] :
      ( ~ r2_hidden(C_27,'#skF_3')
      | ~ r2_hidden(C_27,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_209,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_48),'#skF_4')
      | ~ r1_tarski(A_47,'#skF_3')
      | r1_xboole_0(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_129,c_56])).

tff(c_225,plain,(
    ! [B_7] :
      ( ~ r1_tarski('#skF_4','#skF_3')
      | r1_xboole_0('#skF_4',B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_209])).

tff(c_233,plain,(
    ! [B_49] : r1_xboole_0('#skF_4',B_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_225])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_241,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_233,c_18])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_250,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_8])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.07/1.22  
% 2.07/1.22  %Foreground sorts:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Background operators:
% 2.07/1.22  
% 2.07/1.22  
% 2.07/1.22  %Foreground operators:
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.22  
% 2.07/1.23  tff(f_72, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.07/1.23  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.07/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.07/1.23  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.07/1.23  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.23  tff(c_24, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.23  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.23  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.23  tff(c_41, plain, (![C_22, B_23, A_24]: (r2_hidden(C_22, B_23) | ~r2_hidden(C_22, A_24) | ~r1_tarski(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.23  tff(c_129, plain, (![A_36, B_37, B_38]: (r2_hidden('#skF_2'(A_36, B_37), B_38) | ~r1_tarski(A_36, B_38) | r1_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_14, c_41])).
% 2.07/1.23  tff(c_20, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.07/1.23  tff(c_51, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, B_26) | ~r2_hidden(C_27, A_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.23  tff(c_56, plain, (![C_27]: (~r2_hidden(C_27, '#skF_3') | ~r2_hidden(C_27, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_51])).
% 2.07/1.23  tff(c_209, plain, (![A_47, B_48]: (~r2_hidden('#skF_2'(A_47, B_48), '#skF_4') | ~r1_tarski(A_47, '#skF_3') | r1_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_129, c_56])).
% 2.07/1.23  tff(c_225, plain, (![B_7]: (~r1_tarski('#skF_4', '#skF_3') | r1_xboole_0('#skF_4', B_7))), inference(resolution, [status(thm)], [c_14, c_209])).
% 2.07/1.23  tff(c_233, plain, (![B_49]: (r1_xboole_0('#skF_4', B_49))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_225])).
% 2.07/1.23  tff(c_18, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.07/1.23  tff(c_241, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_233, c_18])).
% 2.07/1.23  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.23  tff(c_250, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_8])).
% 2.07/1.23  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_250])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 42
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 1
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 4
% 2.07/1.23  #Demod        : 15
% 2.07/1.23  #Tautology    : 9
% 2.07/1.23  #SimpNegUnit  : 1
% 2.07/1.23  #BackRed      : 9
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.26
% 2.07/1.23  Parsing              : 0.15
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.20
% 2.07/1.23  Inferencing          : 0.08
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.04
% 2.11/1.23  BG Simplification    : 0.01
% 2.11/1.23  Subsumption          : 0.05
% 2.11/1.23  Abstraction          : 0.01
% 2.11/1.23  MUC search           : 0.00
% 2.11/1.23  Cooper               : 0.00
% 2.11/1.23  Total                : 0.50
% 2.11/1.23  Index Insertion      : 0.00
% 2.11/1.23  Index Deletion       : 0.00
% 2.11/1.23  Index Matching       : 0.00
% 2.11/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
