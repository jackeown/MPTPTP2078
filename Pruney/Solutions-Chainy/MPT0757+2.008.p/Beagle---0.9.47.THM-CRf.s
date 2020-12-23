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
% DateTime   : Thu Dec  3 10:06:32 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   22 (  26 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  56 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ ( ~ r2_xboole_0(A,B)
          & A != B
          & ~ r2_xboole_0(B,A) )
    <=> r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_xboole_1)).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_3,B_5] :
      ( r3_xboole_0(A_3,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    ! [B_14,A_15] :
      ( r2_xboole_0(B_14,A_15)
      | B_14 = A_15
      | r2_xboole_0(A_15,B_14)
      | ~ r3_xboole_0(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [B_16,A_17] :
      ( r2_xboole_0(B_16,A_17)
      | B_16 = A_17
      | r2_xboole_0(A_17,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_17) ) ),
    inference(resolution,[status(thm)],[c_10,c_25])).

tff(c_12,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,
    ( '#skF_2' = '#skF_1'
    | r2_xboole_0('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_12])).

tff(c_70,plain,
    ( '#skF_2' = '#skF_1'
    | r2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_63])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_14,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  %$ r3_xboole_0 > r2_xboole_0 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.81/1.20  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  
% 1.84/1.21  tff(f_60, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.84/1.21  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 1.84/1.21  tff(f_37, axiom, (![A, B]: (~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)) <=> r3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_xboole_1)).
% 1.84/1.21  tff(c_16, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.21  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.21  tff(c_20, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.21  tff(c_18, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.21  tff(c_10, plain, (![A_3, B_5]: (r3_xboole_0(A_3, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.84/1.21  tff(c_25, plain, (![B_14, A_15]: (r2_xboole_0(B_14, A_15) | B_14=A_15 | r2_xboole_0(A_15, B_14) | ~r3_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.84/1.21  tff(c_59, plain, (![B_16, A_17]: (r2_xboole_0(B_16, A_17) | B_16=A_17 | r2_xboole_0(A_17, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_17))), inference(resolution, [status(thm)], [c_10, c_25])).
% 1.84/1.21  tff(c_12, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.84/1.21  tff(c_63, plain, ('#skF_2'='#skF_1' | r2_xboole_0('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_59, c_12])).
% 1.84/1.21  tff(c_70, plain, ('#skF_2'='#skF_1' | r2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_63])).
% 1.84/1.21  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_14, c_70])).
% 1.84/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.21  
% 1.84/1.21  Inference rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Ref     : 0
% 1.84/1.21  #Sup     : 6
% 1.84/1.21  #Fact    : 2
% 1.84/1.21  #Define  : 0
% 1.84/1.21  #Split   : 0
% 1.84/1.21  #Chain   : 0
% 1.84/1.21  #Close   : 0
% 1.84/1.21  
% 1.84/1.21  Ordering : KBO
% 1.84/1.21  
% 1.84/1.21  Simplification rules
% 1.84/1.21  ----------------------
% 1.84/1.21  #Subsume      : 0
% 1.84/1.21  #Demod        : 2
% 1.84/1.21  #Tautology    : 5
% 1.84/1.21  #SimpNegUnit  : 1
% 1.84/1.21  #BackRed      : 0
% 1.84/1.21  
% 1.84/1.21  #Partial instantiations: 0
% 1.84/1.21  #Strategies tried      : 1
% 1.84/1.21  
% 1.84/1.21  Timing (in seconds)
% 1.84/1.21  ----------------------
% 1.84/1.21  Preprocessing        : 0.29
% 1.84/1.21  Parsing              : 0.15
% 1.84/1.21  CNF conversion       : 0.02
% 1.84/1.21  Main loop            : 0.10
% 1.84/1.21  Inferencing          : 0.04
% 1.84/1.21  Reduction            : 0.02
% 1.84/1.21  Demodulation         : 0.02
% 1.84/1.21  BG Simplification    : 0.01
% 1.84/1.21  Subsumption          : 0.02
% 1.84/1.21  Abstraction          : 0.00
% 1.84/1.21  MUC search           : 0.00
% 1.84/1.21  Cooper               : 0.00
% 1.84/1.21  Total                : 0.41
% 1.84/1.21  Index Insertion      : 0.00
% 1.84/1.21  Index Deletion       : 0.00
% 1.84/1.21  Index Matching       : 0.00
% 1.84/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
