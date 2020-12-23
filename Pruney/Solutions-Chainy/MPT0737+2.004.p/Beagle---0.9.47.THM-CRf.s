%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  81 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(c_18,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_53,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ r1_ordinal1(A_16,B_17)
      | ~ v3_ordinal1(B_17)
      | ~ v3_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski(A_10,B_11)
      | r3_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ~ r3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_14])).

tff(c_56,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_53,c_28])).

tff(c_62,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_56])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_19,plain,(
    ! [B_8,A_9] :
      ( ~ r1_tarski(B_8,A_9)
      | r3_xboole_0(A_9,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_19,c_14])).

tff(c_59,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_23])).

tff(c_65,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_59])).

tff(c_70,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_76,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_70])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  %$ r3_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
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
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.10  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.10  
% 1.59/1.11  tff(f_55, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 1.59/1.11  tff(f_47, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.59/1.11  tff(f_31, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 1.59/1.11  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 1.59/1.11  tff(c_18, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.59/1.11  tff(c_16, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.59/1.11  tff(c_53, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~r1_ordinal1(A_16, B_17) | ~v3_ordinal1(B_17) | ~v3_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.59/1.11  tff(c_24, plain, (![A_10, B_11]: (~r1_tarski(A_10, B_11) | r3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.11  tff(c_14, plain, (~r3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.59/1.11  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_14])).
% 1.59/1.11  tff(c_56, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_53, c_28])).
% 1.59/1.11  tff(c_62, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_56])).
% 1.59/1.11  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.59/1.11  tff(c_19, plain, (![B_8, A_9]: (~r1_tarski(B_8, A_9) | r3_xboole_0(A_9, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.11  tff(c_23, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_19, c_14])).
% 1.59/1.11  tff(c_59, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_53, c_23])).
% 1.59/1.11  tff(c_65, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_59])).
% 1.59/1.11  tff(c_70, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_65])).
% 1.59/1.11  tff(c_76, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_70])).
% 1.59/1.11  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_76])).
% 1.59/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  Inference rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Ref     : 0
% 1.59/1.11  #Sup     : 8
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
% 1.59/1.11  #Tautology    : 2
% 1.59/1.11  #SimpNegUnit  : 1
% 1.59/1.11  #BackRed      : 0
% 1.59/1.11  
% 1.59/1.11  #Partial instantiations: 0
% 1.59/1.11  #Strategies tried      : 1
% 1.59/1.11  
% 1.59/1.11  Timing (in seconds)
% 1.59/1.11  ----------------------
% 1.59/1.12  Preprocessing        : 0.24
% 1.59/1.12  Parsing              : 0.13
% 1.59/1.12  CNF conversion       : 0.02
% 1.59/1.12  Main loop            : 0.10
% 1.59/1.12  Inferencing          : 0.05
% 1.59/1.12  Reduction            : 0.02
% 1.59/1.12  Demodulation         : 0.02
% 1.59/1.12  BG Simplification    : 0.01
% 1.59/1.12  Subsumption          : 0.02
% 1.59/1.12  Abstraction          : 0.00
% 1.59/1.12  MUC search           : 0.00
% 1.59/1.12  Cooper               : 0.00
% 1.59/1.12  Total                : 0.37
% 1.59/1.12  Index Insertion      : 0.00
% 1.59/1.12  Index Deletion       : 0.00
% 1.59/1.12  Index Matching       : 0.00
% 1.59/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
