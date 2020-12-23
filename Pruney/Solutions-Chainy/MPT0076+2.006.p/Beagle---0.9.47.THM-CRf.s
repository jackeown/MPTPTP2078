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
% DateTime   : Thu Dec  3 09:43:33 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ~ ( r1_tarski(B,A)
            & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [B_19,A_20] :
      ( r1_xboole_0(B_19,A_20)
      | ~ r1_xboole_0(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_48,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_xboole_0(A_21,C_22)
      | ~ r1_xboole_0(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [A_25] :
      ( r1_xboole_0(A_25,'#skF_3')
      | ~ r1_tarski(A_25,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_43,c_48])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_25] :
      ( r1_xboole_0('#skF_3',A_25)
      | ~ r1_tarski(A_25,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_8])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_92,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r2_hidden(C_32,k2_xboole_0(A_34,B_33))
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [C_39,A_40] :
      ( ~ r2_hidden(C_39,A_40)
      | ~ r2_hidden(C_39,A_40)
      | ~ r2_hidden(C_39,A_40)
      | ~ r1_xboole_0(A_40,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_120,plain,(
    ! [A_41] :
      ( ~ r2_hidden('#skF_1'(A_41),A_41)
      | ~ r1_xboole_0(A_41,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_125,plain,(
    ! [A_42] :
      ( ~ r1_xboole_0(A_42,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_137,plain,
    ( v1_xboole_0('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_154,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_137])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.19  
% 1.99/1.20  tff(f_69, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.99/1.20  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.99/1.20  tff(f_60, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.99/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.99/1.20  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.99/1.20  tff(f_54, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.99/1.20  tff(c_24, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.20  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.20  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.20  tff(c_40, plain, (![B_19, A_20]: (r1_xboole_0(B_19, A_20) | ~r1_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.20  tff(c_43, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_40])).
% 1.99/1.20  tff(c_48, plain, (![A_21, C_22, B_23]: (r1_xboole_0(A_21, C_22) | ~r1_xboole_0(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.20  tff(c_62, plain, (![A_25]: (r1_xboole_0(A_25, '#skF_3') | ~r1_tarski(A_25, '#skF_2'))), inference(resolution, [status(thm)], [c_43, c_48])).
% 1.99/1.20  tff(c_8, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.20  tff(c_68, plain, (![A_25]: (r1_xboole_0('#skF_3', A_25) | ~r1_tarski(A_25, '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_8])).
% 1.99/1.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.20  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.20  tff(c_92, plain, (![C_32, B_33, A_34]: (~r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r2_hidden(C_32, k2_xboole_0(A_34, B_33)) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.20  tff(c_116, plain, (![C_39, A_40]: (~r2_hidden(C_39, A_40) | ~r2_hidden(C_39, A_40) | ~r2_hidden(C_39, A_40) | ~r1_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_92])).
% 1.99/1.20  tff(c_120, plain, (![A_41]: (~r2_hidden('#skF_1'(A_41), A_41) | ~r1_xboole_0(A_41, A_41) | v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_4, c_116])).
% 1.99/1.20  tff(c_125, plain, (![A_42]: (~r1_xboole_0(A_42, A_42) | v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_4, c_120])).
% 1.99/1.20  tff(c_137, plain, (v1_xboole_0('#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_125])).
% 1.99/1.20  tff(c_154, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_137])).
% 1.99/1.20  tff(c_156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_154])).
% 1.99/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.20  
% 1.99/1.20  Inference rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Ref     : 0
% 1.99/1.20  #Sup     : 31
% 1.99/1.20  #Fact    : 0
% 1.99/1.20  #Define  : 0
% 1.99/1.20  #Split   : 1
% 1.99/1.20  #Chain   : 0
% 1.99/1.20  #Close   : 0
% 1.99/1.20  
% 1.99/1.20  Ordering : KBO
% 1.99/1.20  
% 1.99/1.20  Simplification rules
% 1.99/1.20  ----------------------
% 1.99/1.20  #Subsume      : 5
% 1.99/1.20  #Demod        : 3
% 1.99/1.20  #Tautology    : 7
% 1.99/1.20  #SimpNegUnit  : 1
% 1.99/1.20  #BackRed      : 0
% 1.99/1.20  
% 1.99/1.20  #Partial instantiations: 0
% 1.99/1.20  #Strategies tried      : 1
% 1.99/1.20  
% 1.99/1.20  Timing (in seconds)
% 1.99/1.20  ----------------------
% 1.99/1.21  Preprocessing        : 0.27
% 1.99/1.21  Parsing              : 0.15
% 1.99/1.21  CNF conversion       : 0.02
% 1.99/1.21  Main loop            : 0.18
% 1.99/1.21  Inferencing          : 0.07
% 1.99/1.21  Reduction            : 0.04
% 1.99/1.21  Demodulation         : 0.03
% 1.99/1.21  BG Simplification    : 0.01
% 1.99/1.21  Subsumption          : 0.05
% 1.99/1.21  Abstraction          : 0.01
% 1.99/1.21  MUC search           : 0.00
% 1.99/1.21  Cooper               : 0.00
% 1.99/1.21  Total                : 0.48
% 1.99/1.21  Index Insertion      : 0.00
% 1.99/1.21  Index Deletion       : 0.00
% 1.99/1.21  Index Matching       : 0.00
% 1.99/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
