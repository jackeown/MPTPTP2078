%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  66 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_57,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,C_32)
      | ~ r1_xboole_0(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_68,plain,(
    ! [A_34] :
      ( r1_xboole_0(A_34,'#skF_4')
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_61])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_37] :
      ( r1_xboole_0('#skF_4',A_37)
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_68,c_8])).

tff(c_14,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_xboole_0(B_15,C_16)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_248,plain,(
    ! [A_54,A_55] :
      ( r1_xboole_0(A_54,A_55)
      | ~ r1_tarski(A_54,'#skF_4')
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_14])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( ~ r1_xboole_0(A_28,B_29)
      | v1_xboole_0(k3_xboole_0(A_28,B_29)) ) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_59,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_56])).

tff(c_264,plain,(
    ! [A_56] :
      ( v1_xboole_0(A_56)
      | ~ r1_tarski(A_56,'#skF_4')
      | ~ r1_tarski(A_56,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_59])).

tff(c_267,plain,
    ( v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_264])).

tff(c_270,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.32  
% 1.91/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 1.91/1.32  
% 1.91/1.32  %Foreground sorts:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Background operators:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Foreground operators:
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.32  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.32  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.32  
% 2.20/1.33  tff(f_68, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.20/1.33  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.20/1.33  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.20/1.33  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.20/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.20/1.33  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.20/1.33  tff(c_22, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.33  tff(c_18, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.33  tff(c_20, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.33  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.20/1.33  tff(c_61, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, C_32) | ~r1_xboole_0(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.33  tff(c_68, plain, (![A_34]: (r1_xboole_0(A_34, '#skF_4') | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_61])).
% 2.20/1.33  tff(c_8, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.33  tff(c_97, plain, (![A_37]: (r1_xboole_0('#skF_4', A_37) | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_8])).
% 2.20/1.33  tff(c_14, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_xboole_0(B_15, C_16) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.33  tff(c_248, plain, (![A_54, A_55]: (r1_xboole_0(A_54, A_55) | ~r1_tarski(A_54, '#skF_4') | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_97, c_14])).
% 2.20/1.33  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.33  tff(c_46, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.33  tff(c_56, plain, (![A_28, B_29]: (~r1_xboole_0(A_28, B_29) | v1_xboole_0(k3_xboole_0(A_28, B_29)))), inference(resolution, [status(thm)], [c_4, c_46])).
% 2.20/1.33  tff(c_59, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_56])).
% 2.20/1.33  tff(c_264, plain, (![A_56]: (v1_xboole_0(A_56) | ~r1_tarski(A_56, '#skF_4') | ~r1_tarski(A_56, '#skF_3'))), inference(resolution, [status(thm)], [c_248, c_59])).
% 2.20/1.33  tff(c_267, plain, (v1_xboole_0('#skF_5') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_264])).
% 2.20/1.33  tff(c_270, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_267])).
% 2.20/1.33  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_270])).
% 2.20/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  Inference rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Ref     : 0
% 2.20/1.33  #Sup     : 60
% 2.20/1.33  #Fact    : 0
% 2.20/1.33  #Define  : 0
% 2.20/1.33  #Split   : 4
% 2.20/1.33  #Chain   : 0
% 2.20/1.33  #Close   : 0
% 2.20/1.33  
% 2.20/1.33  Ordering : KBO
% 2.20/1.33  
% 2.20/1.33  Simplification rules
% 2.20/1.33  ----------------------
% 2.20/1.33  #Subsume      : 21
% 2.20/1.33  #Demod        : 4
% 2.20/1.33  #Tautology    : 9
% 2.20/1.33  #SimpNegUnit  : 1
% 2.20/1.33  #BackRed      : 0
% 2.20/1.33  
% 2.20/1.33  #Partial instantiations: 0
% 2.20/1.33  #Strategies tried      : 1
% 2.20/1.33  
% 2.20/1.33  Timing (in seconds)
% 2.20/1.33  ----------------------
% 2.20/1.34  Preprocessing        : 0.30
% 2.20/1.34  Parsing              : 0.16
% 2.20/1.34  CNF conversion       : 0.02
% 2.20/1.34  Main loop            : 0.22
% 2.20/1.34  Inferencing          : 0.09
% 2.20/1.34  Reduction            : 0.05
% 2.20/1.34  Demodulation         : 0.03
% 2.20/1.34  BG Simplification    : 0.02
% 2.20/1.34  Subsumption          : 0.05
% 2.20/1.34  Abstraction          : 0.01
% 2.20/1.34  MUC search           : 0.00
% 2.20/1.34  Cooper               : 0.00
% 2.20/1.34  Total                : 0.54
% 2.20/1.34  Index Insertion      : 0.00
% 2.20/1.34  Index Deletion       : 0.00
% 2.20/1.34  Index Matching       : 0.00
% 2.20/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
