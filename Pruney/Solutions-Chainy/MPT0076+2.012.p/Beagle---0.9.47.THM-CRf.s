%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:34 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_16,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_23,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_19,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_35,plain,(
    ! [C_19] :
      ( ~ r1_xboole_0('#skF_4','#skF_3')
      | ~ r2_hidden(C_19,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_32])).

tff(c_43,plain,(
    ! [C_20] : ~ r2_hidden(C_20,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).

tff(c_47,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:46:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.18  
% 1.63/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.79/1.18  
% 1.79/1.18  %Foreground sorts:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Background operators:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Foreground operators:
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.79/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.18  
% 1.79/1.19  tff(f_58, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.79/1.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.79/1.19  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.79/1.19  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.79/1.19  tff(c_16, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.19  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.79/1.19  tff(c_12, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.19  tff(c_14, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.19  tff(c_23, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.79/1.19  tff(c_27, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_14, c_23])).
% 1.79/1.19  tff(c_32, plain, (![A_17, B_18, C_19]: (~r1_xboole_0(A_17, B_18) | ~r2_hidden(C_19, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.19  tff(c_35, plain, (![C_19]: (~r1_xboole_0('#skF_4', '#skF_3') | ~r2_hidden(C_19, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27, c_32])).
% 1.79/1.19  tff(c_43, plain, (![C_20]: (~r2_hidden(C_20, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 1.79/1.19  tff(c_47, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_43])).
% 1.79/1.19  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_47])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 0
% 1.79/1.19  #Sup     : 7
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 0
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 0
% 1.79/1.19  #Demod        : 1
% 1.79/1.19  #Tautology    : 3
% 1.79/1.19  #SimpNegUnit  : 1
% 1.79/1.19  #BackRed      : 0
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.20  Preprocessing        : 0.28
% 1.79/1.20  Parsing              : 0.15
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.09
% 1.79/1.20  Inferencing          : 0.05
% 1.79/1.20  Reduction            : 0.02
% 1.79/1.20  Demodulation         : 0.02
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.01
% 1.79/1.20  Abstraction          : 0.00
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.39
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
