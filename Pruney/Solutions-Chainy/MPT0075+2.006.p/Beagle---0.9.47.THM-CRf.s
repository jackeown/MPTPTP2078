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
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  79 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_xboole_0(A_21,C_22)
      | ~ r1_xboole_0(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    ! [A_24] :
      ( r1_xboole_0(A_24,'#skF_3')
      | ~ r1_tarski(A_24,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_26] :
      ( r1_xboole_0('#skF_3',A_26)
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_57,c_8])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [A_12,A_26] :
      ( r1_xboole_0(A_12,A_26)
      | ~ r1_tarski(A_12,'#skF_3')
      | ~ r1_tarski(A_26,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_71,c_18])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [C_35,B_36,A_37] :
      ( ~ r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r2_hidden(C_35,k2_xboole_0(A_37,B_36))
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,(
    ! [C_45,A_46] :
      ( ~ r2_hidden(C_45,A_46)
      | ~ r2_hidden(C_45,A_46)
      | ~ r2_hidden(C_45,A_46)
      | ~ r1_xboole_0(A_46,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_146,plain,(
    ! [A_47] :
      ( ~ r2_hidden('#skF_1'(A_47),A_47)
      | ~ r1_xboole_0(A_47,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_151,plain,(
    ! [A_48] :
      ( ~ r1_xboole_0(A_48,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_4,c_146])).

tff(c_182,plain,(
    ! [A_49] :
      ( v1_xboole_0(A_49)
      | ~ r1_tarski(A_49,'#skF_3')
      | ~ r1_tarski(A_49,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_76,c_151])).

tff(c_185,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_188,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:51:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  
% 1.98/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.98/1.24  
% 1.98/1.24  %Foreground sorts:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Background operators:
% 1.98/1.24  
% 1.98/1.24  
% 1.98/1.24  %Foreground operators:
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.24  
% 1.98/1.25  tff(f_71, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 1.98/1.25  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.98/1.25  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.25  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.98/1.25  tff(f_54, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.98/1.25  tff(c_26, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_24, plain, (r1_tarski('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_20, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.98/1.25  tff(c_50, plain, (![A_21, C_22, B_23]: (r1_xboole_0(A_21, C_22) | ~r1_xboole_0(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.25  tff(c_57, plain, (![A_24]: (r1_xboole_0(A_24, '#skF_3') | ~r1_tarski(A_24, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_50])).
% 1.98/1.25  tff(c_8, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.25  tff(c_71, plain, (![A_26]: (r1_xboole_0('#skF_3', A_26) | ~r1_tarski(A_26, '#skF_2'))), inference(resolution, [status(thm)], [c_57, c_8])).
% 1.98/1.25  tff(c_18, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.98/1.25  tff(c_76, plain, (![A_12, A_26]: (r1_xboole_0(A_12, A_26) | ~r1_tarski(A_12, '#skF_3') | ~r1_tarski(A_26, '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_18])).
% 1.98/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.25  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.25  tff(c_112, plain, (![C_35, B_36, A_37]: (~r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r2_hidden(C_35, k2_xboole_0(A_37, B_36)) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.25  tff(c_142, plain, (![C_45, A_46]: (~r2_hidden(C_45, A_46) | ~r2_hidden(C_45, A_46) | ~r2_hidden(C_45, A_46) | ~r1_xboole_0(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 1.98/1.25  tff(c_146, plain, (![A_47]: (~r2_hidden('#skF_1'(A_47), A_47) | ~r1_xboole_0(A_47, A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_4, c_142])).
% 1.98/1.25  tff(c_151, plain, (![A_48]: (~r1_xboole_0(A_48, A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_4, c_146])).
% 1.98/1.25  tff(c_182, plain, (![A_49]: (v1_xboole_0(A_49) | ~r1_tarski(A_49, '#skF_3') | ~r1_tarski(A_49, '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_151])).
% 1.98/1.25  tff(c_185, plain, (v1_xboole_0('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_182])).
% 1.98/1.25  tff(c_188, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_185])).
% 1.98/1.25  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_188])).
% 1.98/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  Inference rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Ref     : 0
% 1.98/1.25  #Sup     : 38
% 1.98/1.25  #Fact    : 0
% 1.98/1.25  #Define  : 0
% 1.98/1.25  #Split   : 4
% 1.98/1.25  #Chain   : 0
% 1.98/1.25  #Close   : 0
% 1.98/1.25  
% 1.98/1.25  Ordering : KBO
% 1.98/1.25  
% 1.98/1.25  Simplification rules
% 1.98/1.25  ----------------------
% 1.98/1.25  #Subsume      : 11
% 1.98/1.25  #Demod        : 2
% 1.98/1.25  #Tautology    : 7
% 1.98/1.25  #SimpNegUnit  : 1
% 1.98/1.25  #BackRed      : 0
% 1.98/1.25  
% 1.98/1.25  #Partial instantiations: 0
% 1.98/1.25  #Strategies tried      : 1
% 1.98/1.25  
% 1.98/1.25  Timing (in seconds)
% 1.98/1.25  ----------------------
% 1.98/1.26  Preprocessing        : 0.24
% 1.98/1.26  Parsing              : 0.14
% 1.98/1.26  CNF conversion       : 0.02
% 1.98/1.26  Main loop            : 0.19
% 1.98/1.26  Inferencing          : 0.07
% 1.98/1.26  Reduction            : 0.04
% 1.98/1.26  Demodulation         : 0.03
% 1.98/1.26  BG Simplification    : 0.01
% 1.98/1.26  Subsumption          : 0.05
% 1.98/1.26  Abstraction          : 0.01
% 1.98/1.26  MUC search           : 0.00
% 1.98/1.26  Cooper               : 0.00
% 1.98/1.26  Total                : 0.46
% 1.98/1.26  Index Insertion      : 0.00
% 1.98/1.26  Index Deletion       : 0.00
% 1.98/1.26  Index Matching       : 0.00
% 1.98/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
