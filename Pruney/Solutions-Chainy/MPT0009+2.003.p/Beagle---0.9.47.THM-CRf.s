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
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_44,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_41,plain,(
    ! [A_18,B_19] :
      ( r2_hidden('#skF_2'(A_18,B_19),A_18)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_21,B_22] :
      ( ~ v1_xboole_0(A_21)
      | r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_17,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_16,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_16])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_23])).

tff(c_59,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:31:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  %$ r2_hidden > r1_tarski > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.63/1.11  
% 1.63/1.11  %Foreground sorts:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Background operators:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Foreground operators:
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.63/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.63/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.12  
% 1.63/1.12  tff(f_44, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.63/1.12  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.12  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.63/1.12  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.63/1.12  tff(f_47, negated_conjecture, ~(![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.63/1.12  tff(c_14, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.63/1.12  tff(c_41, plain, (![A_18, B_19]: (r2_hidden('#skF_2'(A_18, B_19), A_18) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.63/1.12  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.12  tff(c_52, plain, (![A_21, B_22]: (~v1_xboole_0(A_21) | r1_tarski(A_21, B_22))), inference(resolution, [status(thm)], [c_41, c_2])).
% 1.63/1.12  tff(c_17, plain, (![A_11]: (k1_xboole_0=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.12  tff(c_21, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_17])).
% 1.63/1.12  tff(c_16, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.63/1.12  tff(c_23, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21, c_16])).
% 1.63/1.12  tff(c_55, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_23])).
% 1.63/1.12  tff(c_59, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_55])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 8
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 0
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 3
% 1.63/1.12  #Tautology    : 4
% 1.63/1.12  #SimpNegUnit  : 0
% 1.63/1.12  #BackRed      : 2
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.13  Preprocessing        : 0.25
% 1.63/1.13  Parsing              : 0.14
% 1.63/1.13  CNF conversion       : 0.02
% 1.63/1.13  Main loop            : 0.10
% 1.63/1.13  Inferencing          : 0.05
% 1.63/1.13  Reduction            : 0.02
% 1.63/1.13  Demodulation         : 0.02
% 1.63/1.13  BG Simplification    : 0.01
% 1.63/1.13  Subsumption          : 0.01
% 1.63/1.13  Abstraction          : 0.00
% 1.63/1.13  MUC search           : 0.00
% 1.63/1.13  Cooper               : 0.00
% 1.63/1.13  Total                : 0.38
% 1.63/1.13  Index Insertion      : 0.00
% 1.63/1.13  Index Deletion       : 0.00
% 1.63/1.13  Index Matching       : 0.00
% 1.63/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
