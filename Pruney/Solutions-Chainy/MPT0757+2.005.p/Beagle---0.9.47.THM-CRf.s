%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   32 (  50 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 115 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_22,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ r1_ordinal1(A_15,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    ! [A_11,B_12] :
      ( r2_xboole_0(A_11,B_12)
      | B_12 = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_31,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_25,c_18])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_31])).

tff(c_58,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_49,c_42])).

tff(c_65,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_58])).

tff(c_80,plain,(
    ! [B_17,A_18] :
      ( r1_ordinal1(B_17,A_18)
      | r1_ordinal1(A_18,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_25,c_14])).

tff(c_45,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_34])).

tff(c_55,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_45])).

tff(c_62,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_55])).

tff(c_84,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_62])).

tff(c_91,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_84])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  %$ r2_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.59/1.10  
% 1.59/1.10  %Foreground sorts:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Background operators:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Foreground operators:
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.10  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.59/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.10  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.59/1.10  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.10  
% 1.59/1.11  tff(f_64, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.59/1.11  tff(f_48, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.59/1.11  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.59/1.11  tff(f_40, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 1.59/1.11  tff(c_22, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.59/1.11  tff(c_20, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.59/1.11  tff(c_49, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~r1_ordinal1(A_15, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.59/1.11  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.59/1.11  tff(c_25, plain, (![A_11, B_12]: (r2_xboole_0(A_11, B_12) | B_12=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.59/1.11  tff(c_18, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.59/1.11  tff(c_31, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_25, c_18])).
% 1.59/1.11  tff(c_42, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_16, c_31])).
% 1.59/1.11  tff(c_58, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_49, c_42])).
% 1.59/1.11  tff(c_65, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_58])).
% 1.59/1.11  tff(c_80, plain, (![B_17, A_18]: (r1_ordinal1(B_17, A_18) | r1_ordinal1(A_18, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.11  tff(c_14, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.59/1.11  tff(c_34, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_25, c_14])).
% 1.59/1.11  tff(c_45, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_34])).
% 1.59/1.11  tff(c_55, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_49, c_45])).
% 1.59/1.11  tff(c_62, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_55])).
% 1.59/1.11  tff(c_84, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_80, c_62])).
% 1.59/1.11  tff(c_91, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_84])).
% 1.59/1.11  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_91])).
% 1.59/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  Inference rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Ref     : 0
% 1.59/1.11  #Sup     : 9
% 1.59/1.11  #Fact    : 2
% 1.59/1.11  #Define  : 0
% 1.59/1.11  #Split   : 0
% 1.59/1.11  #Chain   : 0
% 1.59/1.11  #Close   : 0
% 1.59/1.11  
% 1.59/1.11  Ordering : KBO
% 1.59/1.11  
% 1.59/1.11  Simplification rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Subsume      : 0
% 1.59/1.11  #Demod        : 6
% 1.59/1.11  #Tautology    : 3
% 1.59/1.11  #SimpNegUnit  : 3
% 1.59/1.11  #BackRed      : 0
% 1.59/1.11  
% 1.59/1.11  #Partial instantiations: 0
% 1.59/1.11  #Strategies tried      : 1
% 1.59/1.11  
% 1.59/1.11  Timing (in seconds)
% 1.59/1.11  ----------------------
% 1.59/1.11  Preprocessing        : 0.26
% 1.59/1.11  Parsing              : 0.14
% 1.59/1.11  CNF conversion       : 0.02
% 1.59/1.11  Main loop            : 0.10
% 1.59/1.11  Inferencing          : 0.04
% 1.59/1.11  Reduction            : 0.03
% 1.59/1.11  Demodulation         : 0.01
% 1.59/1.11  BG Simplification    : 0.01
% 1.59/1.11  Subsumption          : 0.02
% 1.59/1.11  Abstraction          : 0.00
% 1.59/1.11  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.11  Total                : 0.38
% 1.59/1.11  Index Insertion      : 0.00
% 1.59/1.11  Index Deletion       : 0.00
% 1.59/1.11  Index Matching       : 0.00
% 1.59/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
