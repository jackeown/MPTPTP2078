%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:31 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
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

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [A_32,C_33,B_34] :
      ( r1_xboole_0(A_32,C_33)
      | ~ r1_xboole_0(B_34,C_33)
      | ~ r1_tarski(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_97,plain,(
    ! [A_35] :
      ( r1_xboole_0(A_35,'#skF_4')
      | ~ r1_tarski(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_37] :
      ( r1_xboole_0('#skF_4',A_37)
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_97,c_6])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_223,plain,(
    ! [A_54,A_55] :
      ( r1_xboole_0(A_54,A_55)
      | ~ r1_tarski(A_54,'#skF_4')
      | ~ r1_tarski(A_55,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_118,c_14])).

tff(c_8,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_294,plain,(
    ! [C_69,A_70,A_71] :
      ( ~ r2_hidden(C_69,A_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,'#skF_4')
      | ~ r1_tarski(A_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_223,c_8])).

tff(c_321,plain,(
    ! [A_78,A_79] :
      ( ~ r2_hidden('#skF_1'(A_78),A_79)
      | ~ r1_tarski(A_79,'#skF_4')
      | ~ r1_tarski(A_78,'#skF_3')
      | v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_4,c_294])).

tff(c_326,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,'#skF_4')
      | ~ r1_tarski(A_80,'#skF_3')
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_321])).

tff(c_329,plain,
    ( ~ r1_tarski('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_326])).

tff(c_332,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.30  
% 2.23/1.31  tff(f_70, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.23/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.31  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.23/1.31  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.23/1.31  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.23/1.31  tff(c_22, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.31  tff(c_18, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.31  tff(c_20, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.31  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.31  tff(c_84, plain, (![A_32, C_33, B_34]: (r1_xboole_0(A_32, C_33) | ~r1_xboole_0(B_34, C_33) | ~r1_tarski(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.31  tff(c_97, plain, (![A_35]: (r1_xboole_0(A_35, '#skF_4') | ~r1_tarski(A_35, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.23/1.31  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.31  tff(c_118, plain, (![A_37]: (r1_xboole_0('#skF_4', A_37) | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_97, c_6])).
% 2.23/1.31  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.31  tff(c_223, plain, (![A_54, A_55]: (r1_xboole_0(A_54, A_55) | ~r1_tarski(A_54, '#skF_4') | ~r1_tarski(A_55, '#skF_3'))), inference(resolution, [status(thm)], [c_118, c_14])).
% 2.23/1.31  tff(c_8, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.31  tff(c_294, plain, (![C_69, A_70, A_71]: (~r2_hidden(C_69, A_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, '#skF_4') | ~r1_tarski(A_70, '#skF_3'))), inference(resolution, [status(thm)], [c_223, c_8])).
% 2.23/1.31  tff(c_321, plain, (![A_78, A_79]: (~r2_hidden('#skF_1'(A_78), A_79) | ~r1_tarski(A_79, '#skF_4') | ~r1_tarski(A_78, '#skF_3') | v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_4, c_294])).
% 2.23/1.31  tff(c_326, plain, (![A_80]: (~r1_tarski(A_80, '#skF_4') | ~r1_tarski(A_80, '#skF_3') | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_321])).
% 2.23/1.31  tff(c_329, plain, (~r1_tarski('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_20, c_326])).
% 2.23/1.31  tff(c_332, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_329])).
% 2.23/1.31  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_332])).
% 2.23/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  Inference rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Ref     : 0
% 2.23/1.31  #Sup     : 72
% 2.23/1.31  #Fact    : 0
% 2.23/1.31  #Define  : 0
% 2.23/1.31  #Split   : 7
% 2.23/1.31  #Chain   : 0
% 2.23/1.31  #Close   : 0
% 2.23/1.31  
% 2.23/1.31  Ordering : KBO
% 2.23/1.31  
% 2.23/1.31  Simplification rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Subsume      : 26
% 2.23/1.31  #Demod        : 4
% 2.23/1.31  #Tautology    : 4
% 2.23/1.31  #SimpNegUnit  : 5
% 2.23/1.31  #BackRed      : 0
% 2.23/1.31  
% 2.23/1.31  #Partial instantiations: 0
% 2.23/1.31  #Strategies tried      : 1
% 2.23/1.31  
% 2.23/1.31  Timing (in seconds)
% 2.23/1.31  ----------------------
% 2.23/1.32  Preprocessing        : 0.27
% 2.23/1.32  Parsing              : 0.15
% 2.23/1.32  CNF conversion       : 0.02
% 2.23/1.32  Main loop            : 0.29
% 2.23/1.32  Inferencing          : 0.11
% 2.23/1.32  Reduction            : 0.06
% 2.23/1.32  Demodulation         : 0.04
% 2.23/1.32  BG Simplification    : 0.02
% 2.23/1.32  Subsumption          : 0.08
% 2.23/1.32  Abstraction          : 0.01
% 2.23/1.32  MUC search           : 0.00
% 2.23/1.32  Cooper               : 0.00
% 2.23/1.32  Total                : 0.59
% 2.23/1.32  Index Insertion      : 0.00
% 2.23/1.32  Index Deletion       : 0.00
% 2.23/1.32  Index Matching       : 0.00
% 2.23/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
