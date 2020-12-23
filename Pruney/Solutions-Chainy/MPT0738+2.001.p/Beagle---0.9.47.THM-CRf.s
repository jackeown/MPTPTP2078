%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:04 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 141 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 419 expanded)
%              Number of equality atoms :   11 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_74,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_24,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_71,plain,(
    ! [B_32,A_33] :
      ( r1_ordinal1(B_32,A_33)
      | r1_ordinal1(A_33,B_32)
      | ~ v3_ordinal1(B_32)
      | ~ v3_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_74,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_26])).

tff(c_80,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_74])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [B_42,A_43] :
      ( r2_hidden(B_42,A_43)
      | B_42 = A_43
      | r2_hidden(A_43,B_42)
      | ~ v3_ordinal1(B_42)
      | ~ v3_ordinal1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,(
    ! [B_55,B_56,A_57] :
      ( r2_hidden(B_55,B_56)
      | ~ r1_tarski(A_57,B_56)
      | B_55 = A_57
      | r2_hidden(A_57,B_55)
      | ~ v3_ordinal1(B_55)
      | ~ v3_ordinal1(A_57) ) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_237,plain,(
    ! [B_65,B_66,A_67] :
      ( r2_hidden(B_65,B_66)
      | B_65 = A_67
      | r2_hidden(A_67,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ r1_ordinal1(A_67,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v3_ordinal1(A_67) ) ),
    inference(resolution,[status(thm)],[c_20,c_215])).

tff(c_241,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_2')
      | B_65 = '#skF_3'
      | r2_hidden('#skF_3',B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1('#skF_2')
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_80,c_237])).

tff(c_249,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_2')
      | B_65 = '#skF_3'
      | r2_hidden('#skF_3',B_65)
      | ~ v3_ordinal1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_241])).

tff(c_252,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_2')
      | B_68 = '#skF_3'
      | r2_hidden('#skF_3',B_68)
      | ~ v3_ordinal1(B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_241])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_282,plain,(
    ! [B_69] :
      ( ~ r2_hidden('#skF_2',B_69)
      | B_69 = '#skF_3'
      | r2_hidden('#skF_3',B_69)
      | ~ v3_ordinal1(B_69) ) ),
    inference(resolution,[status(thm)],[c_252,c_2])).

tff(c_286,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_282])).

tff(c_297,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_286])).

tff(c_298,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_297])).

tff(c_307,plain,(
    r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_80])).

tff(c_308,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_26])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.24  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.24/1.24  
% 2.24/1.24  %Foreground sorts:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Background operators:
% 2.24/1.24  
% 2.24/1.24  
% 2.24/1.24  %Foreground operators:
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.24  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 2.24/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.24  
% 2.24/1.26  tff(f_84, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 2.24/1.26  tff(f_51, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 2.24/1.26  tff(f_59, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 2.24/1.26  tff(f_74, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 2.24/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.24/1.26  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.24/1.26  tff(c_24, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.26  tff(c_30, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.26  tff(c_28, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.26  tff(c_71, plain, (![B_32, A_33]: (r1_ordinal1(B_32, A_33) | r1_ordinal1(A_33, B_32) | ~v3_ordinal1(B_32) | ~v3_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.26  tff(c_26, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.26  tff(c_74, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_26])).
% 2.24/1.26  tff(c_80, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_74])).
% 2.24/1.26  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.26  tff(c_132, plain, (![B_42, A_43]: (r2_hidden(B_42, A_43) | B_42=A_43 | r2_hidden(A_43, B_42) | ~v3_ordinal1(B_42) | ~v3_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.24/1.26  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.26  tff(c_215, plain, (![B_55, B_56, A_57]: (r2_hidden(B_55, B_56) | ~r1_tarski(A_57, B_56) | B_55=A_57 | r2_hidden(A_57, B_55) | ~v3_ordinal1(B_55) | ~v3_ordinal1(A_57))), inference(resolution, [status(thm)], [c_132, c_4])).
% 2.24/1.26  tff(c_237, plain, (![B_65, B_66, A_67]: (r2_hidden(B_65, B_66) | B_65=A_67 | r2_hidden(A_67, B_65) | ~v3_ordinal1(B_65) | ~r1_ordinal1(A_67, B_66) | ~v3_ordinal1(B_66) | ~v3_ordinal1(A_67))), inference(resolution, [status(thm)], [c_20, c_215])).
% 2.24/1.26  tff(c_241, plain, (![B_65]: (r2_hidden(B_65, '#skF_2') | B_65='#skF_3' | r2_hidden('#skF_3', B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_80, c_237])).
% 2.24/1.26  tff(c_249, plain, (![B_65]: (r2_hidden(B_65, '#skF_2') | B_65='#skF_3' | r2_hidden('#skF_3', B_65) | ~v3_ordinal1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_241])).
% 2.24/1.26  tff(c_252, plain, (![B_68]: (r2_hidden(B_68, '#skF_2') | B_68='#skF_3' | r2_hidden('#skF_3', B_68) | ~v3_ordinal1(B_68))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_241])).
% 2.24/1.26  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.24/1.26  tff(c_282, plain, (![B_69]: (~r2_hidden('#skF_2', B_69) | B_69='#skF_3' | r2_hidden('#skF_3', B_69) | ~v3_ordinal1(B_69))), inference(resolution, [status(thm)], [c_252, c_2])).
% 2.24/1.26  tff(c_286, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_249, c_282])).
% 2.24/1.26  tff(c_297, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_286])).
% 2.24/1.26  tff(c_298, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_24, c_297])).
% 2.24/1.26  tff(c_307, plain, (r1_ordinal1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_80])).
% 2.24/1.26  tff(c_308, plain, (~r1_ordinal1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_26])).
% 2.24/1.26  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_308])).
% 2.24/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  Inference rules
% 2.24/1.26  ----------------------
% 2.24/1.26  #Ref     : 0
% 2.24/1.26  #Sup     : 53
% 2.24/1.26  #Fact    : 4
% 2.24/1.26  #Define  : 0
% 2.24/1.26  #Split   : 0
% 2.24/1.26  #Chain   : 0
% 2.24/1.26  #Close   : 0
% 2.24/1.26  
% 2.24/1.26  Ordering : KBO
% 2.24/1.26  
% 2.24/1.26  Simplification rules
% 2.24/1.26  ----------------------
% 2.24/1.26  #Subsume      : 13
% 2.24/1.26  #Demod        : 27
% 2.24/1.26  #Tautology    : 20
% 2.24/1.26  #SimpNegUnit  : 1
% 2.24/1.26  #BackRed      : 5
% 2.24/1.26  
% 2.24/1.26  #Partial instantiations: 0
% 2.24/1.26  #Strategies tried      : 1
% 2.24/1.26  
% 2.24/1.26  Timing (in seconds)
% 2.24/1.26  ----------------------
% 2.24/1.26  Preprocessing        : 0.27
% 2.24/1.26  Parsing              : 0.15
% 2.24/1.26  CNF conversion       : 0.02
% 2.24/1.26  Main loop            : 0.24
% 2.24/1.26  Inferencing          : 0.10
% 2.24/1.26  Reduction            : 0.06
% 2.24/1.26  Demodulation         : 0.04
% 2.24/1.26  BG Simplification    : 0.02
% 2.24/1.26  Subsumption          : 0.06
% 2.24/1.26  Abstraction          : 0.01
% 2.24/1.26  MUC search           : 0.00
% 2.24/1.26  Cooper               : 0.00
% 2.24/1.26  Total                : 0.53
% 2.24/1.26  Index Insertion      : 0.00
% 2.24/1.26  Index Deletion       : 0.00
% 2.24/1.26  Index Matching       : 0.00
% 2.24/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
